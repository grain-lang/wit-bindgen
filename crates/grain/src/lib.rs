use std::{
    collections::{HashMap, HashSet},
    fmt::Write,
    mem,
};

use heck::*;
use wit_bindgen_core::{
    abi::{self, AbiVariant, Bindgen, Bitcast, Instruction, LiftLower, WasmType},
    dealias, uwrite, uwriteln,
    wit_parser::{
        self, Case, Docs, Enum, EnumCase, Flags, FlagsRepr, Function, FunctionKind, Handle, Int,
        Interface, InterfaceId, Record, Resolve, Result_, SizeAlign, Tuple, Type, TypeDef,
        TypeDefKind, TypeId, TypeOwner, Variant, WorldId, WorldKey,
    },
    Files, InterfaceGenerator, Ns, Source, TypeInfo, Types, WorldGenerator,
};

use heck::{ToLowerCamelCase, ToUpperCamelCase};

#[derive(Default, Debug, Clone)]
#[cfg_attr(feature = "clap", derive(clap::Args))]
pub struct Opts {}

impl Opts {
    pub fn build(&self) -> Box<dyn WorldGenerator> {
        Box::new(Grain {
            _opts: self.clone(),
            ..Grain::default()
        })
    }
}

#[derive(Default)]
pub struct Grain {
    _opts: Opts,
    src: Source,
    world: String,
    types: Types,
    sizes: SizeAlign,
    interface_names: HashMap<InterfaceId, WorldKey>,
    /// Each imported and exported interface is stored in this map. Value indicates if last use was import.
    interface_last_seen_as_import: HashMap<InterfaceId, bool>,

    // Interfaces who have had their types printed.
    //
    // This is used to guard against printing the types for an interface twice.
    // The same interface can be both imported and exported in which case only
    // one set of types is generated and all bindings for both imports and
    // exports use that set of types.
    interfaces_with_types_printed: HashSet<InterfaceId>,
    return_pointer_area_size: usize,
}

impl Grain {
    fn interface<'a>(
        &'a mut self,
        wasm_import_module: Option<&'a str>,
        resolve: &'a Resolve,
        name: &'a Option<&'a WorldKey>,
        in_import: bool,
    ) -> GrainInterfaceGenerator<'a> {
        GrainInterfaceGenerator {
            wasm_import_module,
            src: Source::default(),
            gen: self,
            resolve,
            interface: None,
            name,
            in_import,
            export_funcs: Vec::new(),
        }
    }

    // fn finish_types(&mut self, resolve: &Resolve) {
    //     for (id, _) in resolve.types.iter() {
    //         if let Some((_, ty)) = self.types.get(&id) {
    //             self.src.push_str(&ty);
    //         }
    //     }
    // }
}

impl GrainGenerator for GrainInterfaceGenerator<'_> {
    fn push_str(&mut self, s: &str) {
        self.src.push_str(s);
    }

    fn info(&self, ty: TypeId) -> TypeInfo {
        self.gen.types.get(ty)
    }
}

impl WorldGenerator for Grain {
    fn preprocess(&mut self, resolve: &Resolve, world: WorldId) {
        let name = &resolve.worlds[world].name;
        self.world = name.to_string();
        self.sizes.fill(resolve);
    }
    fn import_interface(
        &mut self,
        resolve: &Resolve,
        name: &WorldKey,
        id: InterfaceId,
        _files: &mut Files,
    ) {
        self.interface_last_seen_as_import.insert(id, true);
        let wasm_import_module = resolve.name_world_key(name);
        // self.src
        //     .push_str(&format!("// Import functions from {wasm_import_module}\n"));
        self.interface_names.insert(id, name.clone());
        
        let binding = Some(name);
        let mut gen = self.interface(Some(&wasm_import_module), resolve, &binding, true);
        gen.interface = Some(id);
        if gen.gen.interfaces_with_types_printed.insert(id) {
            gen.types(id);
        }

        let resources: Vec<&TypeId> = resolve.interfaces[id]
            .types
            .iter()
            .filter_map(|t| match resolve.types[*(t.1)].kind {
                TypeDefKind::Resource => Some(t.1),
                _ => None,
            })
            .collect();

        let freestanding_funcs: Vec<(&String, &Function)> = resolve.interfaces[id]
            .functions
            .iter()
            .filter(|f| match f.1.kind {
                FunctionKind::Freestanding => true,
                _ => false,
            })
            .collect();

        gen.src.push_str(&format!("\n\n"));

        gen.src.push_str("provide module ");
        gen.src.push_str(
            &resolve.interfaces[id]
                .name
                .as_ref()
                .unwrap()
                .to_upper_camel_case(),
        );
        gen.src.push_str(" {\n");
        for (_name, func) in freestanding_funcs.iter() {
            gen.src.push_str("\n");
            gen.import(resolve, func);
        }
        for resource in resources.iter() {
            let resource_funcs: Vec<(&String, &Function)> = resolve.interfaces[id]
                .functions
                .iter()
                .filter(|f| match f.1.kind {
                    FunctionKind::Method(id)
                    | FunctionKind::Constructor(id)
                    | FunctionKind::Static(id)
                        if **resource == id =>
                    {
                        true
                    }
                    _ => false,
                })
                .collect();

            gen.src.push_str("\nprovide module ");
            gen.src.push_str(
                &resolve.types[**resource]
                    .name
                    .as_ref()
                    .unwrap()
                    .to_upper_camel_case(),
            );
            gen.src.push_str(" {");
            for (_name, func) in resource_funcs.iter() {
                gen.src.push_str("\n");
                gen.import(resolve, func);
            }
            gen.src.push_str("}\n");
        }
        gen.src.push_str("}\n\n");
        gen.finish();

        let src = mem::take(&mut gen.src);
        self.src.push_str(&src);
    }
    fn import_funcs(
        &mut self,
        resolve: &Resolve,
        world: WorldId,
        funcs: &[(&str, &Function)],
        _files: &mut Files,
    ) {
        let name = &resolve.worlds[world].name;
        self.src
            .push_str(&format!("// Import functions from {name}\n"));

        let mut gen = self.interface(Some("$root"), resolve, &None, true);
        for (_name, func) in funcs.iter() {
            gen.import(resolve, func);
        }
        gen.finish();

        let src = mem::take(&mut gen.src);
        self.src.push_str(&src);
    }

    fn import_types(
        &mut self,
        resolve: &Resolve,
        world: WorldId,
        types: &[(&str, TypeId)],
        _files: &mut Files,
    ) {
        let mut gen = self.interface(Some("$root"), resolve, &None, false);
        for (name, id) in types {
            gen.define_type(name, *id);
        }
        gen.finish();
        let src = mem::take(&mut gen.src);
        self.src.push_str(&src);
    }

    fn export_funcs(
        &mut self,
        resolve: &Resolve,
        world: WorldId,
        funcs: &[(&str, &Function)],
        _files: &mut Files,
    ) -> anyhow::Result<()> {
        let name = &resolve.worlds[world].name;
        self.src
            .push_str(&format!("// Export functions from {name}\n"));

        let mut gen = self.interface(None, resolve, &None, false);
        for (_name, func) in funcs.iter() {
            gen.export(resolve, func, *gen.name);
        }

        gen.finish();

        let src = mem::take(&mut gen.src);
        self.src.push_str(&src);
        Ok(())
    }

    fn export_interface(
        &mut self,
        resolve: &Resolve,
        name: &WorldKey,
        id: InterfaceId,
        _files: &mut Files,
    ) -> anyhow::Result<()> {
        self.interface_last_seen_as_import.insert(id, false);
        self.interface_names.insert(id, name.clone());
        let name_raw = &resolve.name_world_key(name);
        self.src
            .push_str(&format!("// Export functions from {name_raw}\n"));

        let binding = Some(name);
        let mut gen = self.interface(None, resolve, &binding, false);
        gen.interface = Some(id);
        if gen.gen.interfaces_with_types_printed.insert(id) {
            gen.types(id);
        }

        let resources: Vec<&TypeId> = resolve.interfaces[id]
            .types
            .iter()
            .filter_map(|t| match resolve.types[*(t.1)].kind {
                TypeDefKind::Resource => Some(t.1),
                _ => None,
            })
            .collect();

        let freestanding_funcs: Vec<(&String, &Function)> = resolve.interfaces[id]
            .functions
            .iter()
            .filter(|f| match f.1.kind {
                FunctionKind::Freestanding => true,
                _ => false,
            })
            .collect();

        gen.src.push_str("\nmodule ");
        gen.src.push_str(
            &resolve.interfaces[id]
                .name
                .as_ref()
                .unwrap()
                .to_upper_camel_case(),
        );
        gen.src.push_str("Exports {");
        for (_name, func) in freestanding_funcs.iter() {
            gen.src.push_str("\n");
            gen.export_stub(resolve, func, Some(name));
        }
        for resource in resources.iter() {
            let resource_funcs: Vec<(&String, &Function)> = resolve.interfaces[id]
                .functions
                .iter()
                .filter(|f| match f.1.kind {
                    FunctionKind::Method(id)
                    | FunctionKind::Constructor(id)
                    | FunctionKind::Static(id)
                        if **resource == id =>
                    {
                        true
                    }
                    _ => false,
                })
                .collect();

            gen.src.push_str("\nprovide module ");
            gen.src.push_str(
                &resolve.types[**resource]
                    .name
                    .as_ref()
                    .unwrap()
                    .to_upper_camel_case(),
            );
            gen.src.push_str(" {");
            for (_name, func) in resource_funcs.iter() {
                gen.src.push_str("\n");
                gen.export_stub(resolve, func, Some(name));
            }
            gen.src.push_str("}\n");
        }
        gen.src.push_str("}\n\n");

        for (_name, func) in resolve.interfaces[id].functions.iter() {
            gen.export(resolve, func, Some(name));
        }

        gen.finish();

        let src = mem::take(&mut gen.src);
        self.src.push_str(&src);
        Ok(())
    }

    fn finish(
        &mut self,
        resolve: &Resolve,
        world: WorldId,
        files: &mut Files,
    ) -> Result<(), anyhow::Error> {
        let world = &resolve.worlds[world];
        let mut full_src = Source::default();

        full_src.push_str(&format!("module {}\n\n", world.name.to_upper_camel_case()));

        // TODO: Selectively include only used libraries
        full_src.push_str("from \"runtime/dataStructures\" include DataStructures\n");
        full_src.push_str("from \"runtime/unsafe/wasmi32\" include WasmI32\n");
        full_src.push_str("from \"runtime/unsafe/wasmi64\" include WasmI64\n");
        full_src.push_str("from \"runtime/unsafe/wasmf32\" include WasmF32\n");
        full_src.push_str("from \"runtime/unsafe/wasmf64\" include WasmF64\n");
        full_src.push_str("from \"runtime/unsafe/memory\" include Memory\n");
        full_src.push_str("from \"int32\" include Int32\n");
        full_src.push_str("from \"int64\" include Int64\n");
        full_src.push_str("from \"char\" include Char\n");
        full_src.push_str("from \"list\" include List\n");

        full_src.push_str("\n");

        if self.return_pointer_area_size > 0 {
            full_src.push_str("@unsafe\n");
            full_src.push_str(&format!(
                "let _RET_AREA = Memory.malloc({}n)\n\n",
                self.return_pointer_area_size
            ));
        }

        full_src.push_str("@unsafe\n");
        full_src.push_str("provide let cabi_realloc = (originalPtr: WasmI32, originalSize: WasmI32, alignment: WasmI32, newSize: WasmI32) => {\n");
        full_src.push_str("if (WasmI32.eqz(originalPtr)) {\n");
        full_src.push_str("Memory.malloc(newSize)\n");
        full_src.push_str("} else {\n");
        full_src.push_str("let newPtr = Memory.malloc(newSize)\n");
        full_src.push_str(
            "let amt = if (WasmI32.(<)(originalSize, newSize)) originalSize else newSize\n",
        );
        full_src.push_str("Memory.copy(newPtr, originalPtr, amt)\n");
        full_src.push_str("Memory.free(originalPtr)\n");
        full_src.push_str("newPtr\n");
        full_src.push_str("}\n");
        full_src.push_str("}\n\n");

        full_src.push_str("provide record Resource<a> {\n");
        full_src.push_str("mut handle: Int32,\n");
        full_src.push_str("rep: a\n");
        full_src.push_str("}\n\n");

        full_src.push_str(self.src.as_mut_string());

        files.push(
            &format!("{}.gr", world.name.to_lower_camel_case()),
            full_src.as_bytes(),
        );

        Ok(())
    }
}

pub struct GrainInterfaceGenerator<'a> {
    wasm_import_module: Option<&'a str>,
    src: Source,
    gen: &'a mut Grain,
    resolve: &'a Resolve,
    interface: Option<InterfaceId>,
    name: &'a Option<&'a WorldKey>,
    in_import: bool,
    export_funcs: Vec<(String, String)>,
}

impl GrainInterfaceGenerator<'_> {
    pub fn is_empty_type(&mut self, ty: &TypeDef) -> bool {
        match &ty.kind {
            TypeDefKind::Type(t) => {
                let def = match t {
                    Type::Id(id) => &self.resolve().types[*id],
                    _ => return false,
                };
                self.is_empty_type(def)
            }
            TypeDefKind::Record(r) => r.fields.is_empty(),
            TypeDefKind::Tuple(t) => t.types.is_empty(),
            _ => false,
        }
    }

    pub fn is_exported_resource(&self, ty: TypeId) -> bool {
        let ty = dealias(self.resolve, ty);
        let ty = &self.resolve.types[ty];
        match &ty.kind {
            TypeDefKind::Resource => {}
            _ => return false,
        }

        match ty.owner {
            // Worlds cannot export types of any kind as of this writing.
            TypeOwner::World(_) => false,

            // Interfaces are "stateful" currently where whatever we last saw
            // them as dictates whether it's exported or not.
            TypeOwner::Interface(i) => !self.gen.interface_last_seen_as_import[&i],

            // Shouldn't be the case for resources
            TypeOwner::None => unreachable!(),
        }
    }

    fn print_tydef(&mut self, ty: &TypeDefKind) {
        match ty {
            TypeDefKind::Type(t) => self.print_ty(t),
            TypeDefKind::List(Type::Char) => self.src.push_str("String"),
            TypeDefKind::List(Type::U8) => self.src.push_str("Bytes"),
            TypeDefKind::List(t) => {
                self.src.push_str("List<");
                self.print_ty(t);
                self.src.push_str(">");
            }
            TypeDefKind::Option(t) => {
                self.src.push_str("Option<");
                self.print_ty(t);
                self.src.push_str(">");
            }
            TypeDefKind::Result(Result_ { ok, err }) => {
                self.src.push_str("Result<");
                match ok {
                    Some(ty) => self.print_ty(ty),
                    None => self.src.push_str("Void"),
                }
                self.src.push_str(", ");
                match err {
                    Some(ty) => self.print_ty(ty),
                    None => self.src.push_str("Void"),
                }
                self.src.push_str(">");
            }
            TypeDefKind::Tuple(Tuple { types }) => {
                if types.len() == 0 {
                    // Grain does not have zero-length tuples
                    self.src.push_str("Void");
                    return;
                }
                self.src.push_str("(");
                for (i, ty) in types.iter().enumerate() {
                    if i != 0 {
                        self.src.push_str(", ");
                    }
                    self.print_ty(ty);
                }
                self.src.push_str(")");
            }
            TypeDefKind::Handle(Handle::Own(ty)) => {
                self.print_ty(&Type::Id(*ty));
            }
            TypeDefKind::Handle(Handle::Borrow(ty)) => {
                // is_exported_resource
                self.print_ty(&Type::Id(*ty));
            }
            _ => {
                unreachable!()
            }
        }
    }

    fn print_ty(&mut self, ty: &Type) {
        match ty {
            Type::Bool => self.src.push_str("Bool"),
            Type::U8 => self.src.push_str("Uint8"),
            Type::S8 => self.src.push_str("Int8"),
            Type::U16 => self.src.push_str("Uint16"),
            Type::S16 => self.src.push_str("Int16"),
            Type::U32 => self.src.push_str("Uint32"),
            Type::S32 => self.src.push_str("Int32"),
            Type::U64 => self.src.push_str("Uint64"),
            Type::S64 => self.src.push_str("Int64"),
            Type::Float32 => self.src.push_str("Float32"),
            Type::Float64 => self.src.push_str("Float64"),
            Type::Char => self.src.push_str("Char"),
            Type::String => self.src.push_str("String"),
            Type::Id(id) => {
                let types = &self.resolve().types;
                let ty = &types[*id];
                if self.is_empty_type(&ty) {
                    self.src.push_str("Void");
                    return;
                }
                if let Some(name) = &ty.name {
                    self.src.push_str(&name.to_upper_camel_case());
                    return;
                }
                self.print_tydef(&ty.kind);
            }
        }
    }

    fn print_func_signature(&mut self, resolve: &Resolve, func: &Function) {
        todo!()
    }

    fn import(&mut self, resolve: &Resolve, func: &Function) {
        let sig = FnSig::default();
        let wasm_sig = resolve.wasm_signature(AbiVariant::GuestImport, func);
        self.src.push_str("@externalName(\"");
        self.src.push_str(&func.name);
        self.src.push_str("\")\n");
        self.src.push_str("foreign wasm ");
        self.push_str("wit_bindgen_");
        self.push_str(&to_grain_ident(&func.name));
        self.push_str(": (");
        let params: Vec<&str> = wasm_sig
            .params
            .iter()
            .map(|param| wasm_type(*param))
            .collect();
        self.push_str(&params.join(", "));
        self.push_str(") -> ");
        match wasm_sig.results.len() {
            0 => self.push_str("Void"),
            1 => {
                for result in wasm_sig.results.iter() {
                    self.push_str(wasm_type(*result));
                }
            }
            _ => {
                panic!("multivalue");
            }
        }
        self.push_str(" from ");
        self.push_str(&format!(
            "\"{}\"",
            self.wasm_import_module.unwrap().to_string()
        ));
        self.src.push_str("\n\n");
        let params = self.print_signature(resolve, func, &sig);
        self.src.push_str(" => {\n");

        let mut func_bindgen = FunctionBindgen::new(self, params);
        abi::call(
            resolve,
            AbiVariant::GuestImport,
            LiftLower::LowerArgsLiftResults,
            func,
            &mut func_bindgen,
        );
        let FunctionBindgen {
            // needs_cleanup_list,
            src,
            // import_return_pointer_area_size,
            // import_return_pointer_area_align,
            ..
        } = func_bindgen;

        // if needs_cleanup_list {
        //     self.src.push_str("let mut cleanup_list = Vec::new();\n");
        // }
        // if import_return_pointer_area_size > 0 {
        //     uwrite!(
        //         self.src,
        //         "
        //             #[repr(align({import_return_pointer_area_align}))]
        //             struct RetArea([u8; {import_return_pointer_area_size}]);
        //             let mut ret_area = ::core::mem::MaybeUninit::<RetArea>::uninit();
        //         ",
        //     );
        // }
        self.src.push_str(&String::from(src));

        // lower params to c
        // func.params.iter().for_each(|(name, ty)| {
        //     func_bindgen.lower(&name, ty, false);
        // });
        // // lift results from c
        // match func.results.len() {
        //     0 => {}
        //     1 => {
        //         let ty = func.results.iter_types().next().unwrap();
        //         func_bindgen.lift("ret", ty);
        //     }
        //     _ => {
        //         for (i, ty) in func.results.iter_types().enumerate() {
        //             func_bindgen.lift(&format!("ret{i}"), ty);
        //         }
        //     }
        // };

        // let lowered_args = func_bindgen.lowered_args;
        // let ret = func_bindgen.lifted_args;
        // let lowered_src = func_bindgen.lowered_src.to_string();
        // let lifted_src = func_bindgen.lifted_src.to_string();

        // body
        // prepare args
        // self.src.push_str(lowered_src.as_str());

        // self.import_invoke(resolve, func, lowered_args, &lifted_src, ret);

        // return

        self.src.push_str("}\n\n");
    }

    fn import_invoke(
        &mut self,
        resolve: &Resolve,
        func: &Function,
        lowered_args: Vec<String>,
        lift_src: &str,
        ret: Vec<String>,
    ) {
        todo!()
    }

    fn export(&mut self, resolve: &Resolve, func: &Function, interface_name: Option<&WorldKey>) {
        let wasm_module_export_name = interface_name.map(|k| self.resolve.name_world_key(k));
        let export_name = func.core_export_name(wasm_module_export_name.as_deref());

        self.src.push_str("@unsafe\n");
        self.src.push_str("@externalName(\"");
        self.src.push_str(&export_name);
        self.src.push_str("\")\n");
        self.src.push_str("provide let ");
        self.src.push_str(&to_grain_ident(
            &func
                .core_export_name(wasm_module_export_name.as_deref())
                .replace('.', "_")
                .replace(':', "_"),
        ));
        self.src.push_str(" = (");
        let sig = resolve.wasm_signature(AbiVariant::GuestExport, func);
        let mut params = Vec::new();
        let mut is_first = true;
        for (i, param) in sig.params.iter().enumerate() {
            if is_first {
                is_first = false;
            } else {
                self.src.push_str(", ");
            }
            let name = format!("arg{}", i);
            self.src.push_str(&name);
            self.src.push_str(": ");
            self.wasm_type(*param);
            params.push(name);
        }
        self.src.push_str(") => {\n");

        let mut f = FunctionBindgen::new(self, params);
        abi::call(
            resolve,
            AbiVariant::GuestExport,
            LiftLower::LiftArgsLowerResults,
            func,
            &mut f,
        );
        let FunctionBindgen {
            // needs_cleanup_list,
            src,
            ..
        } = f;
        // assert!(!needs_cleanup_list);
        self.src.push_str(&String::from(src));
        self.src.push_str("}\n\n");
    }

    fn export_stub(
        &mut self,
        resolve: &Resolve,
        func: &Function,
        interface_name: Option<&WorldKey>,
    ) {
        self.src.push_str("provide let ");
        self.src.push_str(&to_grain_ident(&func.item_name()));
        self.src.push_str(" = (");
        let length = func.params.len();
        for (i, (name, param)) in func.params.iter().enumerate() {
            self.src.push_str(&to_grain_ident(name));
            self.src.push_str(": ");
            self.print_ty(param);
            if i < length - 1 {
                self.push_str(", ");
            }
        }
        self.src.push_str(") => {\n");
        self.src.push_str("(fail \"unimplemented\"): ");
        self.print_results(resolve, func);
        self.src.push_str("\n");
        self.src.push_str("}\n");
    }

    fn finish(&mut self) {
        // todo!()
    }
}

impl<'a> InterfaceGenerator<'a> for GrainInterfaceGenerator<'a> {
    fn resolve(&self) -> &'a Resolve {
        self.resolve
    }

    fn type_record(
        &mut self,
        id: TypeId,
        name: &str,
        record: &wit_parser::Record,
        docs: &wit_parser::Docs,
    ) {
        if record.fields.is_empty() {
            // Empty records don't exist in Grain
            self.src.push_str(&format!(
                "provide type {r} = Void\n",
                r = name.to_upper_camel_case()
            ));
            return;
        }

        self.src.push_str(&format!(
            "provide record {r} {{",
            r = name.to_upper_camel_case()
        ));
        for (_i, field) in record.fields.iter().enumerate() {
            self.src
                .push_str(&format!("\n{f}: ", f = to_grain_ident(&field.name)));
            self.print_ty(&field.ty);
            self.src.push_str(",");
        }
        self.src.push_str("\n}\n")
    }

    fn type_resource(&mut self, id: TypeId, name: &str, docs: &wit_parser::Docs) {
        let name = to_grain_ident(name);
        let name_upper = name.to_upper_camel_case();
        let module = match self.resolve.types[id].owner {
            TypeOwner::World(_) => unimplemented!("resource exports from worlds"),
            TypeOwner::Interface(id) => self.resolve.name_world_key(&WorldKey::Interface(id)),
            TypeOwner::None => unimplemented!("should be impossible"),
        };

        if self.in_import {
            self.src.push_str("provide record ");
            self.src.push_str(&name.to_upper_camel_case());
            self.src.push_str(" {\n");
            self.src.push_str("handle: Int32\n");
            self.src.push_str("}\n");
        } else {
            self.src.push_str("provide type ");
            self.src.push_str(&name_upper);
            self.src.push_str(" = Resource<Void>\n");

            self.src.push_str(&format!(
                r#"
@externalName("[resource-new]{name}")
foreign wasm new{name_upper}: WasmI32 -> WasmI32 from "[export]{module}"

@externalName("[resource-rep]{name}")
foreign wasm rep{name_upper}: WasmI32 -> WasmI32 from "[export]{module}"

@unsafe
let new{name_upper} = (rep) => {{
  let v = {{handle: 0l, rep}}
  let ptr = WasmI32.fromGrain(v)
  Memory.incRef(ptr)
  let handle = new{name_upper}(ptr)
  let handle = WasmI32.toGrain(DataStructures.newInt32(handle)): Int32
  v.handle = handle
  v: {name_upper}
}}
"#
            ))
        }
    }

    fn type_flags(&mut self, id: TypeId, name: &str, flags: &Flags, docs: &wit_parser::Docs) {
        let typename = name.to_lower_camel_case();
        let ty = int_repr(flags_repr(flags));
        self.src
            .push_str(&format!("provide type {typename} = {ty}\n\n"));
        let repr = flags_repr(flags);
        for (i, field) in flags.flags.iter().enumerate() {
            self.src.push_str(&format!(
                "provide let _{}_{}: {typename} = {}.shl(1{}, {}{})\n",
                name.to_shouty_snake_case(),
                field.name.to_shouty_snake_case(),
                int_repr(repr),
                int_suffix(repr),
                i,
                int_suffix(repr),
            ));
        }
        self.src.push_str("\n");
    }

    fn type_tuple(
        &mut self,
        _id: TypeId,
        name: &str,
        tuple: &wit_parser::Tuple,
        _docs: &wit_parser::Docs,
    ) {
        self.src.push_str(&format!(
            "provide type {t} = (",
            t = name.to_upper_camel_case()
        ));
        if tuple.types.len() == 1 {
            self.print_ty(&tuple.types[0]);
        } else {
            for (_i, ty) in tuple.types.iter().enumerate() {
                self.print_ty(&ty);
                self.src.push_str(",");
            }
        }
        self.src.push_str(")\n")
    }

    fn type_variant(
        &mut self,
        id: TypeId,
        name: &str,
        variant: &wit_parser::Variant,
        docs: &wit_parser::Docs,
    ) {
        self.src.push_str(&format!(
            "provide enum {r} {{",
            r = name.to_upper_camel_case()
        ));
        for case in variant.cases.iter() {
            self.src.push_str("\n");
            self.src.push_str(&case_name(&case.name));
            if let Some(ty) = case.ty {
                self.src.push_str("(");
                self.print_ty(&ty);
                self.src.push_str(")")
            }
            self.src.push_str(",");
        }
        self.src.push_str("\n}\n");
    }

    fn type_option(&mut self, _id: TypeId, _name: &str, _payload: &Type, _docs: &wit_parser::Docs) {
        // No type needed
    }

    fn type_result(
        &mut self,
        id: TypeId,
        name: &str,
        result: &wit_parser::Result_,
        docs: &wit_parser::Docs,
    ) {
        // No type needed
    }

    fn type_enum(
        &mut self,
        id: TypeId,
        name: &str,
        enum_: &wit_parser::Enum,
        docs: &wit_parser::Docs,
    ) {
        self.src.push_str(&format!(
            "provide enum {r} {{",
            r = name.to_upper_camel_case()
        ));
        for case in enum_.cases.iter() {
            self.src.push_str("\n");
            self.src.push_str(&case_name(&case.name));
            self.src.push_str(",");
        }
        self.src.push_str("\n}\n");
    }

    fn type_alias(&mut self, id: TypeId, name: &str, ty: &Type, docs: &wit_parser::Docs) {
        let is_unnecessary_alias = match ty {
            Type::Id(ty_id) => self.resolve.types[*ty_id].name == self.resolve.types[id].name,
            _ => false
        };
        if !is_unnecessary_alias {
            self.src.push_str(&format!(
                "provide type {t} = ",
                t = name.to_upper_camel_case()
            ));
            self.print_ty(ty);
            self.src.push_str("\n")
        }
    }

    fn type_list(&mut self, id: TypeId, name: &str, ty: &Type, docs: &wit_parser::Docs) {
        self.src.push_str(&format!(
            "provide type {t} = ",
            t = name.to_upper_camel_case()
        ));
        match ty {
            Type::Char => self.push_str("String\n"),
            Type::U8 => self.push_str("Bytes\n"),
            _ => {
                self.src.push_str("List<");
                self.print_ty(ty);
                self.src.push_str(">\n");
            }
        }
    }

    fn type_builtin(&mut self, id: TypeId, name: &str, ty: &Type, docs: &wit_parser::Docs) {
        // No type needed
    }
}

struct FunctionBindgen<'a, 'b> {
    interface: &'a mut GrainInterfaceGenerator<'b>,
    locals: Ns,
    src: Source,
    block_storage: Vec<wit_bindgen_core::Source>,
    blocks: Vec<(String, Vec<String>)>,
    payloads: Vec<String>,
    params: Vec<String>,
    return_pointer_area_size: usize,
}

impl<'a, 'b> FunctionBindgen<'a, 'b> {
    fn new(interface: &'a mut GrainInterfaceGenerator<'b>, params: Vec<String>) -> Self {
        Self {
            interface,
            locals: Default::default(),
            src: Default::default(),
            block_storage: Vec::new(),
            blocks: Vec::new(),
            payloads: Vec::new(),
            params,
            return_pointer_area_size: 0,
        }
    }

    // fn lower(&mut self, name: &str, ty: &Type, _in_export: bool) {
    //     match ty {
    //         Type::Bool => self.lower_bool(name),
    //         Type::U8 => self.lower_u8(name),
    //         Type::U16 => self.lower_u16(name),
    //         Type::U32 => self.lower_u32(name),
    //         Type::U64 => self.lower_u64(name),
    //         Type::S8 => self.lower_s8(name),
    //         Type::S16 => self.lower_s16(name),
    //         Type::S32 => self.lower_s32(name),
    //         Type::S64 => self.lower_s64(name),
    //         Type::Float32 => self.lower_f32(name),
    //         Type::Float64 => self.lower_f64(name),
    //         Type::Char => self.lower_char(name),
    //         Type::String => self.lower_string(name),
    //         Type::Id(_) => self.lower_id(name),
    //     }
    // }

    // fn lift(&mut self, name: &str, ty: &Type) {
    //     match ty {
    //         Type::Bool => self.lift_bool(name),
    //         Type::U8 => self.lift_u8(name),
    //         Type::U16 => self.lift_u16(name),
    //         Type::U32 => self.lift_u32(name),
    //         Type::U64 => self.lift_u64(name),
    //         Type::S8 => self.lift_s8(name),
    //         Type::S16 => self.lift_s16(name),
    //         Type::S32 => self.lift_s32(name),
    //         Type::S64 => self.lift_s64(name),
    //         Type::Float32 => self.lift_f32(name),
    //         Type::Float64 => self.lift_f64(name),
    //         Type::Char => self.lift_char(name),
    //         Type::String => self.lift_string(name),
    //         Type::Id(_) => self.lift_id(name),
    //     }
    // }

    // fn lower_bool(&mut self, param: &str, result) {
    //     let mut vec = Vec::new();
    //     vec.push(format!("WasmI32.(>>)(WasmI32.fromGrain({}), 31n)", name));
    //     vec
    // }

    // fn lift_bool(&mut self, param: &str, result) {
    //     let mut vec = Vec::new();
    //     vec.push(format!(
    //         "WasmI32.toGrain(WasmI32.(|)(WasmI32.(<<)({}, 31n), WasmI32.fromGrain(false))): Bool",
    //         name
    //     ));
    //     vec
    // }

    // fn lower_u8(&mut self, param: &str, result) {
    //     let mut vec = Vec::new();
    //     vec.push(format!("WasmI32.(>>>)(WasmI32.fromGrain({}), 8n)", name));
    //     vec
    // }

    // fn lift_u8(&mut self, param: &str, result) {
    //     let mut vec = Vec::new();
    // vec.push(format!(
    //     "WasmI32.toGrain(WasmI32.(|)(WasmI32.(<<)({}, 8n), WasmI32.fromGrain(0us))): Uint8",
    //     name
    // ));
    //     vec
    // }

    // fn lower_u16(&mut self, param: &str, result) {
    //     let mut vec = Vec::new();
    //     vec.push(format!("WasmI32.(>>>)(WasmI32.fromGrain({}), 8n)", name));
    //     vec
    // }

    // fn lift_u16(&mut self, param: &str, result) {
    //     let mut vec = Vec::new();
    //     vec.push(format!(
    //         "WasmI32.toGrain(WasmI32.(|)(WasmI32.(<<)({}, 8n), WasmI32.fromGrain(0uS))): Uint16",
    //         name
    //     ));
    //     vec
    // }

    // fn lower_u32(&mut self, param: &str, result) {
    //     let mut vec = Vec::new();
    //     vec.push(format!("WasmI32.load(WasmI32.fromGrain({}), 4n)", name));
    //     vec
    // }

    // fn lift_u32(&mut self, param: &str, result) {
    //     let mut vec = Vec::new();
    //     vec.push(format!(
    //         "WasmI32.toGrain(DataStructures.newUint32({})): Uint32",
    //         name
    //     ));
    //     vec
    // }

    // fn lower_u64(&mut self, param: &str, result) {
    //     let mut vec = Vec::new();
    //     vec.push(format!("WasmI64.load(WasmI32.fromGrain({}), 8n)", name));
    //     vec
    // }

    // fn lift_u64(&mut self, param: &str, result) {
    //     let mut vec = Vec::new();
    //     vec.push(format!(
    //         "WasmI32.toGrain(DataStructures.newUint64({})): Uint64",
    //         name
    //     ));
    //     vec
    // }

    // fn lower_s8(&mut self, param: &str, result) {
    //     let mut vec = Vec::new();
    //     vec.push(format!("WasmI32.(>>)(WasmI32.fromGrain({}), 8n)", name));
    //     vec
    // }

    // fn lift_s8(&mut self, param: &str, result) {
    //     let mut vec = Vec::new();
    //     vec.push(format!(
    //         "WasmI32.toGrain(WasmI32.(|)(WasmI32.(<<)({}, 8n), WasmI32.fromGrain(0s))): Int8",
    //         name
    //     ));
    //     vec
    // }

    // fn lower_s16(&mut self, param: &str, result) {
    //     let mut vec = Vec::new();
    //     vec.push(format!("WasmI32.(>>)(WasmI32.fromGrain({}), 8n)", name));
    //     vec
    // }

    // fn lift_s16(&mut self, param: &str, result) {
    //     let mut vec = Vec::new();
    //     vec.push(format!(
    //         "WasmI32.toGrain(WasmI32.(|)(WasmI32.(<<)({}, 8n), WasmI32.fromGrain(0S))): Int16",
    //         name
    //     ));
    //     vec
    // }

    // fn lower_s32(&mut self, param: &str, result) {
    //     let mut vec = Vec::new();
    //     vec.push(format!("WasmI32.load(WasmI32.fromGrain({}), 8n)", name));
    //     vec
    // }

    // fn lift_s32(&mut self, param: &str, result) {
    //     let mut vec = Vec::new();
    //     vec.push(format!(
    //         "WasmI32.toGrain(DataStructures.newInt32({})): Int32",
    //         name
    //     ));
    //     vec
    // }

    // fn lower_s64(&mut self, param: &str, result) {
    //     let mut vec = Vec::new();
    //     vec.push(format!("WasmI64.load(WasmI32.fromGrain({}), 8n)", name));
    //     vec
    // }

    // fn lift_s64(&mut self, param: &str, result) {
    //     let mut vec = Vec::new();
    //     vec.push(format!(
    //         "WasmI32.toGrain(DataStructures.newUint64({})): Int64",
    //         name
    //     ));
    //     vec
    // }

    // fn lower_f32(&mut self, param: &str, result) {
    //     let mut vec = Vec::new();
    //     vec.push(format!("WasmF32.load(WasmI32.fromGrain({}), 4n)", name,));
    //     vec
    // }

    // fn lift_f32(&mut self, param: &str, result) {
    //     let mut vec = Vec::new();
    //     vec.push(format!(
    //         "WasmI32.toGrain(DataStructures.newFloat32({})): Float32",
    //         name,
    //     ));
    //     vec
    // }

    // fn lower_f64(&mut self, param: &str, result) {
    //     let mut vec = Vec::new();
    //     vec.push(format!("WasmF64.load(WasmI32.fromGrain({}), 8n)", name,));
    //     vec
    // }

    // fn lift_f64(&mut self, param: &str, result) {
    //     let mut vec = Vec::new();
    //     vec.push(format!(
    //         "WasmI32.toGrain(DataStructures.newFloat64({})): Float64",
    //         name,
    //     ));
    //     vec
    // }

    // fn lower_char(&mut self, param: &str, result) {
    //     let mut vec = Vec::new();
    //     vec.push(format!("WasmI32.(>>>)(WasmI32.fromGrain({}), 8n)", name));
    //     vec
    // }

    // fn lift_char(&mut self, param: &str, result) {
    //     let mut vec = Vec::new();
    //     vec.push(format!(
    //         "WasmI32.toGrain(WasmI32.(|)(WasmI32.(<<)({}, 8n), WasmI32.fromGrain('\0'))): Char",
    //         name
    //     ));
    //     vec
    // }

    // fn lower_string(&mut self, param: &str, result) {
    //     todo!()
    // }

    // fn lift_string(&mut self, param: &str, result) {
    //     todo!()
    // }

    // fn lower_id(&mut self, param: &str, result) {
    //     todo!()
    // }

    // fn lift_id(&mut self, param: &str, result) {
    //     todo!()
    // }
}

pub trait GrainGenerator {
    fn push_str(&mut self, s: &str);
    fn info(&self, ty: TypeId) -> TypeInfo;

    fn graindoc(&mut self, docs: &Docs) {
        let docs = match &docs.contents {
            Some(docs) => docs,
            None => return,
        };
        for line in docs.trim().lines() {
            self.push_str("/// ");
            self.push_str(line);
            self.push_str("\n");
        }
    }

    fn graindoc_params(&mut self, docs: &[(String, Type)], header: &str) {
        drop((docs, header));
        // let docs = docs
        //     .iter()
        //     .filter(|param| param.docs.trim().len() > 0)
        //     .collect::<Vec<_>>();
        // if docs.len() == 0 {
        //     return;
        // }

        // self.push_str("///\n");
        // self.push_str("/// ## ");
        // self.push_str(header);
        // self.push_str("\n");
        // self.push_str("///\n");

        // for param in docs {
        //     for (i, line) in param.docs.lines().enumerate() {
        //         self.push_str("/// ");
        //         // Currently wasi only has at most one return value, so there's no
        //         // need to indent it or name it.
        //         if header != "Return" {
        //             if i == 0 {
        //                 self.push_str("* `");
        //                 self.push_str(to_grain_ident(param.name.as_str()));
        //                 self.push_str("` - ");
        //             } else {
        //                 self.push_str("  ");
        //             }
        //         }
        //         self.push_str(line);
        //         self.push_str("\n");
        //     }
        // }
    }

    fn print_signature(&mut self, resolve: &Resolve, func: &Function, sig: &FnSig) -> Vec<String> {
        self.print_docs_and_params(resolve, func, &sig)
    }
    fn print_docs_and_params(
        &mut self,
        resolve: &Resolve,
        func: &Function,
        sig: &FnSig,
    ) -> Vec<String> {
        self.graindoc(&func.docs);
        self.push_str("@unsafe\n");
        if !sig.exported {
            self.push_str("provide ");
        }
        self.push_str("let ");
        let func_name = &func.item_name();
        self.push_str(&to_grain_ident(&func_name));
        self.push_str(": (");
        let mut params = Vec::new();
        let length = func.params.len();
        for (i, (_, param)) in func.params.iter().enumerate() {
            self.print_ty(resolve, param);
            if i < length - 1 {
                self.push_str(", ");
            }
        }
        self.push_str(") -> ");
        self.print_results(resolve, func);
        self.push_str(" = (");
        for (i, (name, _)) in func.params.iter().enumerate() {
            let name = to_grain_ident(name);
            self.push_str(&name);
            params.push(name);
            if i < length - 1 {
                self.push_str(", ");
            }
        }
        self.push_str(")");
        params
    }

    fn print_results(&mut self, resolve: &Resolve, func: &Function) {
        match func.results.len() {
            0 => self.push_str("Void"),
            1 => {
                self.print_ty(resolve, func.results.iter_types().next().unwrap());
            }
            _ => {
                self.push_str("(");
                for ty in func.results.iter_types() {
                    self.print_ty(resolve, ty);
                    self.push_str(", ")
                }
                self.push_str(")")
            }
        }
    }

    fn print_tydef(&mut self, resolve: &Resolve, ty: &TypeDefKind) {
        match ty {
            TypeDefKind::Type(t) => self.print_ty(resolve, t),
            TypeDefKind::List(Type::Char) => self.push_str("String"),
            TypeDefKind::List(Type::U8) => self.push_str("Bytes"),
            TypeDefKind::List(t) => {
                self.push_str("List<");
                self.print_ty(resolve, t);
                self.push_str(">");
            }
            TypeDefKind::Option(t) => {
                self.push_str("Option<");
                self.print_ty(resolve, t);
                self.push_str(">");
            }
            TypeDefKind::Result(Result_ { ok, err }) => {
                self.push_str("Result<");
                match ok {
                    Some(ok) => self.print_ty(resolve, ok),
                    None => self.push_str("Void"),
                }
                self.push_str(", ");
                match err {
                    Some(err) => self.print_ty(resolve, err),
                    None => self.push_str("Void"),
                }
                self.push_str(">");
            }
            TypeDefKind::Tuple(Tuple { types }) => {
                if types.len() == 0 {
                    // Grain does not have zero-length tuples
                    self.push_str("Void");
                    return;
                }
                self.push_str("(");
                for (i, ty) in types.iter().enumerate() {
                    if i != 0 {
                        self.push_str(", ");
                    }
                    self.print_ty(resolve, ty);
                }
                self.push_str(")");
            }
            TypeDefKind::Handle(Handle::Own(ty)) => {
                self.print_ty(resolve, &Type::Id(*ty));
            }
            TypeDefKind::Handle(Handle::Borrow(ty)) => {
                // is_exported_resource
                self.print_ty(resolve, &Type::Id(*ty));
            }
            _ => {
                unreachable!()
            }
        }
    }
    fn print_ty(&mut self, resolve: &Resolve, ty: &Type) {
        match ty {
            Type::Bool => self.push_str("Bool"),
            Type::U8 => self.push_str("Uint8"),
            Type::S8 => self.push_str("Int8"),
            Type::U16 => self.push_str("Uint16"),
            Type::S16 => self.push_str("Int16"),
            Type::U32 => self.push_str("Uint32"),
            Type::S32 => self.push_str("Int32"),
            Type::U64 => self.push_str("Uint64"),
            Type::S64 => self.push_str("Int64"),
            Type::Float32 => self.push_str("Float32"),
            Type::Float64 => self.push_str("Float64"),
            Type::Char => self.push_str("Char"),
            Type::String => self.push_str("String"),
            // Type::Handle(id) => {
            //     self.push_str(&resolve.resources[*id].name.to_camel_case());
            // }
            Type::Id(id) => {
                if is_empty_type(resolve, ty) {
                    self.push_str("Void");
                    return;
                }
                let ty = &resolve.types[*id];
                if let Some(name) = &ty.name {
                    self.push_str(&name.to_upper_camel_case());
                    return;
                }
                self.print_tydef(resolve, &ty.kind);
            }
        }
    }

    fn print_tyid(&mut self, resolve: &Resolve, id: TypeId) {
        let ty = &resolve.types[id];
        if ty.name.is_some() {
            let name = self.result_name(resolve, id);
            self.push_str(&name);
            return;
        }

        match &ty.kind {
            TypeDefKind::List(t) => self.print_list(resolve, t),
            TypeDefKind::Tuple(t) => {
                self.push_str("(");
                // Note the trailing comma after each member to
                // appropriately handle 1-tuples.
                for field in t.types.iter() {
                    self.print_ty(resolve, &field);
                    self.push_str(",");
                }
                self.push_str(")");
            }
            TypeDefKind::Type(t) => self.print_ty(resolve, t),
            _ => {
                panic!("unsupported anonymous type reference")
            }
        }
    }

    fn print_list(&mut self, resolve: &Resolve, ty: &Type) {
        match ty {
            Type::Char => self.push_str("String"),
            _ => {
                self.push_str("List<");
                self.print_ty(resolve, ty);
                self.push_str(">");
            }
        }
    }

    fn int_repr(&mut self, repr: Int) {
        self.push_str(int_repr(repr));
    }

    fn wasm_type(&mut self, ty: WasmType) {
        self.push_str(wasm_type(ty));
    }

    fn param_name(&self, resolve: &Resolve, ty: TypeId) -> String {
        to_grain_ident(resolve.types[ty].name.as_ref().unwrap())
    }

    fn result_name(&self, resolve: &Resolve, ty: TypeId) -> String {
        to_grain_ident(resolve.types[ty].name.as_ref().unwrap())
    }
}

#[derive(Default)]
pub struct FnSig {
    pub rec: bool,
    pub exported: bool,
}

pub trait GrainFunctionGenerator {
    fn push_str(&mut self, s: &str);
    fn tmp(&mut self, name: &str) -> String;
    fn grain_gen(&self) -> &dyn GrainGenerator;
    fn lift_lower(&self) -> LiftLower;

    fn let_results(&mut self, amt: usize, results: &mut Vec<String>) {
        match amt {
            0 => {}
            1 => {
                let tmp = self.tmp("result");
                self.push_str("let ");
                self.push_str(&tmp);
                results.push(tmp);
                self.push_str(" = ");
            }
            n => {
                let tmp = self.tmp("result");
                self.push_str("let (");
                for i in 0..n {
                    let arg = format!("{}_{}", tmp, i);
                    self.push_str(&arg);
                    self.push_str(",");
                    results.push(arg);
                }
                self.push_str(") = ");
            }
        }
    }

    fn tuple_lower(
        &mut self,
        _iface: &Interface,
        _id: TypeId,
        tuple: &Tuple,
        operand: &str,
        results: &mut Vec<String>,
    ) {
        let tmp = self.tmp("tuple_lower");
        let length = tuple.types.len();
        if length == 0 {
            return;
        }
        self.push_str("let (");
        for i in 0..length {
            let arg = format!("{}_{}", tmp, i);
            self.push_str(&arg);
            if i < length - 1 {
                self.push_str(", ");
            }
            results.push(arg);
        }
        if length == 1 {
            self.push_str(",")
        }
        self.push_str(") = ");
        self.push_str(operand);
        self.push_str("\n");
    }

    fn tuple_lift(
        &mut self,
        _iface: &Interface,
        _id: TypeId,
        _ty: &Tuple,
        operands: &[String],
        results: &mut Vec<String>,
    ) {
        if operands.len() == 0 {
            results.push("void".to_string());
        } else if operands.len() == 1 {
            results.push(format!("({},)", operands[0]));
        } else {
            results.push(format!("({})", operands.join(", ")));
        }
    }

    fn record_lower(
        &mut self,
        resolve: &Resolve,
        id: TypeId,
        record: &Record,
        operand: &str,
        results: &mut Vec<String>,
    ) {
        let tmp = self.tmp("record_lower");
        // if record.is_tuple() {
        //     let length = record.fields.len();
        //     if length == 0 {
        //         return;
        //     }
        //     self.push_str("let (");
        //     for i in 0..length {
        //         let arg = format!("t{}_{}", tmp, i);
        //         self.push_str(&arg);
        //         if i < length - 1 {
        //             self.push_str(", ");
        //         }
        //         results.push(arg);
        //     }
        //     if length == 1 {
        //         self.push_str(",")
        //     }
        //     self.push_str(") = ");
        //     self.push_str(operand);
        //     self.push_str("\n");
        // } else {
        let num_fields = record.fields.len();
        if num_fields > 0 {
            self.push_str("let ");
            self.push_str("{ ");
            for (i, field) in record.fields.iter().enumerate() {
                let name = to_grain_ident(&field.name);
                let arg = format!("{}{}", name, tmp);
                self.push_str(&name);
                self.push_str(": ");
                self.push_str(&arg);
                if i < num_fields - 1 {
                    self.push_str(", ");
                }
                results.push(arg);
            }
            let name = self.typename_lower(resolve, id);
            self.push_str(&format!(" }}: {} = ", name));
            self.push_str(operand);
            self.push_str("\n");
        }
    }

    fn record_lift(
        &mut self,
        _iface: &Interface,
        _id: TypeId,
        ty: &Record,
        operands: &[String],
        results: &mut Vec<String>,
    ) {
        // if ty.is_tuple() {
        //     if operands.len() == 0 {
        //         results.push("void".to_string());
        //     } else if operands.len() == 1 {
        //         results.push(format!("({},)", operands[0]));
        //     } else {
        //         results.push(format!("({})", operands.join(", ")));
        //     }
        // } else {
        if operands.len() > 0 {
            let mut result = String::new();
            result.push_str("{ ");
            let num_fields = ty.fields.len();
            for ((i, field), val) in ty.fields.iter().enumerate().zip(operands) {
                result.push_str(&to_grain_ident(&field.name));
                result.push_str(": ");
                result.push_str(&val);
                if i < num_fields - 1 {
                    result.push_str(", ");
                }
            }
            result.push_str(" }");
            results.push(result);
        } else {
            results.push("void".to_string())
        }
    }

    fn typename_lower(&self, resolve: &Resolve, id: TypeId) -> String {
        match self.lift_lower() {
            LiftLower::LowerArgsLiftResults => self
                .grain_gen()
                .param_name(resolve, id)
                .to_upper_camel_case(),
            LiftLower::LiftArgsLowerResults => self
                .grain_gen()
                .result_name(resolve, id)
                .to_upper_camel_case(),
        }
    }

    fn typename_lift(&self, resolve: &Resolve, id: TypeId) -> String {
        match self.lift_lower() {
            LiftLower::LiftArgsLowerResults => self
                .grain_gen()
                .param_name(resolve, id)
                .to_upper_camel_case(),
            LiftLower::LowerArgsLiftResults => self
                .grain_gen()
                .result_name(resolve, id)
                .to_upper_camel_case(),
        }
    }

    fn enum_lower(
        &mut self,
        resolve: &Resolve,
        id: TypeId,
        enum_: &Enum,
        operand: &str,
        results: &mut Vec<String>,
    ) {
        let has_name = resolve.types[id].name.is_some();
        let mut result_operand = String::new();

        let tmp = self.tmp("enum_lower");
        results.push(tmp.to_string());
        result_operand.push_str(&format!("let mut {} = 0n\n", tmp));
        result_operand.push_str("match (");
        result_operand.push_str(operand);
        result_operand.push_str(") {\n");
        for (i, case) in enum_.cases.iter().enumerate() {
            if has_name {
                let name = self.typename_lower(resolve, id);
                result_operand.push_str(&case_name(&case.name));
                result_operand.push_str(": ");
                result_operand.push_str(&name);
            } else {
                unimplemented!()
            }
            result_operand.push_str(" => {\n");
            result_operand.push_str(&format!("{} = {}n\n", tmp, i));
            result_operand.push_str("},\n");
        }
        result_operand.push_str("}\n");
        self.push_str(&result_operand);
    }

    fn enum_lift_case(
        &mut self,
        resolve: &Resolve,
        id: TypeId,
        case: &EnumCase,
        result: &mut String,
    ) {
        if resolve.types[id].name.is_some() {
            // result.push_str("::");
            result.push_str(&case_name(&case.name));
        } else {
            unimplemented!()
        }
    }

    fn variant_lower(
        &mut self,
        resolve: &Resolve,
        id: TypeId,
        variant: &Variant,
        result_types: &&[WasmType],
        operand: &str,
        results: &mut Vec<String>,
        blocks: Vec<(String, Vec<String>)>,
    ) {
        let has_name = resolve.types[id].name.is_some();
        let mut result_operand = String::new();

        let tmp = self.tmp("variant_lower");
        for (i, ty) in result_types.iter().enumerate() {
            results.push(format!("{}_{}", tmp, i));
            let initial_value = wasm_zero(*ty);
            result_operand.push_str(&format!(
                "let mut {} = {}\n",
                format!("{}_{}", tmp, i),
                initial_value
            ))
        }
        result_operand.push_str("match (");
        result_operand.push_str(operand);
        result_operand.push_str(") {\n");
        for (case, block) in variant.cases.iter().zip(blocks) {
            if has_name {
                let name = self.typename_lower(resolve, id);
                result_operand.push_str(&case_name(&case.name));

                if let Some(_) = &case.ty {
                    result_operand.push_str("(e)")
                }

                result_operand.push_str(": ");
                result_operand.push_str(&name);
            } else {
                unimplemented!()
            }
            result_operand.push_str(" => {\n");
            let (block_src, block_operands) = block;
            result_operand.push_str(&block_src);
            for (i, op) in block_operands.iter().enumerate() {
                result_operand.push_str(&format!("{} = {}\n", format!("result{}_{}", tmp, i), op))
            }
            result_operand.push_str("},\n");
        }
        result_operand.push_str("}\n");
        self.push_str(&result_operand);
    }

    fn variant_lift_case(
        &mut self,
        resolve: &Resolve,
        id: TypeId,
        case: &Case,
        block: &(String, Vec<String>),
        result: &mut String,
    ) {
        let (block, ops) = block;
        result.push_str(block);
        let args = &ops.join(", ");
        if resolve.types[id].name.is_some() {
            // result.push_str(&self.typename_lift(resolve, id));
            // result.push_str("::");
            result.push_str(&case_name(&case.name));
            if ops.len() > 0 {
                result.push_str("(");
                result.push_str(args);
                result.push_str(")");
            }
        } else {
            unimplemented!()
        }
    }
}

impl GrainFunctionGenerator for FunctionBindgen<'_, '_> {
    fn push_str(&mut self, s: &str) {
        self.src.push_str(s);
    }

    fn tmp(&mut self, name: &str) -> String {
        self.locals.tmp(name)
    }

    fn grain_gen(&self) -> &dyn GrainGenerator {
        self.interface
    }

    fn lift_lower(&self) -> LiftLower {
        if self.interface.in_import {
            LiftLower::LowerArgsLiftResults
        } else {
            LiftLower::LiftArgsLowerResults
        }
    }
}

impl Bindgen for FunctionBindgen<'_, '_> {
    type Operand = String;

    fn sizes(&self) -> &SizeAlign {
        &self.interface.gen.sizes
    }

    fn push_block(&mut self) {
        let prev = mem::take(&mut self.src);
        self.block_storage.push(prev);
    }

    fn finish_block(&mut self, operands: &mut Vec<String>) {
        let to_restore = self.block_storage.pop().unwrap();
        let src = mem::replace(&mut self.src, to_restore);
        self.blocks.push((src.into(), mem::take(operands)));
    }

    fn return_pointer(&mut self, size: usize, align: usize) -> String {
        self.interface.gen.return_pointer_area_size =
            self.interface.gen.return_pointer_area_size.max(size);
        "_RET_AREA".into()
    }

    fn is_list_canonical(&self, resolve: &Resolve, ty: &Type) -> bool {
        match ty {
            // Lists of u8 are Grain Bytes
            Type::U8 => true,
            _ => false,
        }
    }

    fn emit(
        &mut self,
        resolve: &Resolve,
        inst: &Instruction<'_>,
        operands: &mut Vec<String>,
        results: &mut Vec<String>,
    ) {
        match inst {
            Instruction::GetArg { nth } => results.push(self.params[*nth].clone()),
            Instruction::I32Const { val } => results.push(format!("{}n", val)),
            Instruction::ConstZero { tys } => {
                for ty in tys.iter() {
                    results.push(wasm_zero(*ty).to_string())
                }
            }

            // TODO: checked?
            Instruction::U8FromI32 => results.push(format!(
                "WasmI32.toGrain(WasmI32.(|)(WasmI32.(<<)({}, 8n), WasmI32.fromGrain(0us))): Uint8",
                operands[0]
            )),
            Instruction::S8FromI32 => results.push(format!(
                "WasmI32.toGrain(WasmI32.(|)(WasmI32.(<<)({}, 8n), WasmI32.fromGrain(0s))): Int8",
                operands[0]
            )),
            Instruction::U16FromI32 => results.push(format!(
                "WasmI32.toGrain(WasmI32.(|)(WasmI32.(<<)({}, 8n), WasmI32.fromGrain(0uS))): Uint16",
                operands[0]
            )),
            Instruction::S16FromI32 => results.push(format!(
                "WasmI32.toGrain(WasmI32.(|)(WasmI32.(<<)({}, 8n), WasmI32.fromGrain(0S))): Int16",
                operands[0]
            )),
            Instruction::U32FromI32 => results.push(format!(
                "WasmI32.toGrain(DataStructures.newUint32({})): Uint32",
                operands[0]
            )),
            Instruction::S32FromI32 => results.push(format!(
                "WasmI32.toGrain(DataStructures.newInt32({})): Int32",
                operands[0]
            )),
            Instruction::U64FromI64 => results.push(format!(
                "WasmI32.toGrain(DataStructures.newUint64({})): Uint64",
                operands[0]
            )),
            Instruction::S64FromI64 => results.push(format!(
                "WasmI32.toGrain(DataStructures.newInt64({})): Int64",
                operands[0]
            )),

            Instruction::I32FromU8 | Instruction::I32FromU16 => {
                results.push(format!(
                    "WasmI32.(>>>)(WasmI32.fromGrain({}), 8n)",
                    operands[0]
                ));
            }
            Instruction::I32FromS8 | Instruction::I32FromS16 => {
                results.push(format!(
                    "WasmI32.(>>)(WasmI32.fromGrain({}), 8n)",
                    operands[0]
                ));
            }
            Instruction::I32FromU32 => {
                results.push(format!(
                    "WasmI32.load(WasmI32.fromGrain({}), 4n)",
                    operands[0]
                ));
            }
            Instruction::I32FromS32 => {
                results.push(format!(
                    "WasmI32.load(WasmI32.fromGrain({}), 4n)",
                    operands[0]
                ));
            }
            Instruction::I64FromS64 | Instruction::I64FromU64 => {
                results.push(format!(
                    "WasmI64.load(WasmI32.fromGrain({}), 8n)",
                    operands[0]
                ));
            }

            Instruction::F32FromFloat32 => {
                results.push(format!(
                    "WasmF32.load(WasmI32.fromGrain({}), 4n)",
                    operands[0]
                ));
            }
            Instruction::F64FromFloat64 => {
                results.push(format!(
                    "WasmF64.load(WasmI32.fromGrain({}), 8n)",
                    operands[0]
                ));
            }
            Instruction::Float32FromF32 => {
                results.push(format!(
                    "WasmI32.toGrain(DataStructures.newFloat32({})): Float32",
                    operands[0]
                ));
            }
            Instruction::Float64FromF64 => {
                results.push(format!(
                    "WasmI32.toGrain(DataStructures.newFloat64({})): Float64",
                    operands[0]
                ));
            }

            // TODO: checked
            Instruction::CharFromI32 => {
                results.push(format!("WasmI32.toGrain(WasmI32.(|)(WasmI32.(<<)({}, 8n), WasmI32.fromGrain('\\0'))): Char", operands[0]));
            }
            Instruction::I32FromChar => {
                results.push(format!(
                    "WasmI32.(>>>)(WasmI32.fromGrain({}), 8n)",
                    operands[0]
                ));
            }

            Instruction::Bitcasts { casts } => {
                crate::bitcast(casts, operands, results)
            }

            Instruction::I32FromBool => results.push(format!(
                "WasmI32.(>>)(WasmI32.fromGrain({}), 31n)",
                operands[0].clone()
            )),

            Instruction::BoolFromI32 => results.push(format!(
                "WasmI32.toGrain(WasmI32.(|)(WasmI32.(<<)({}, 31n), WasmI32.fromGrain(false))): Bool",
                operands[0].clone()
            )),

            Instruction::RecordLower { ty, record, .. } => {
                let tmp = self.locals.tmp("record");
                let op = &operands[0];
                let num_fields = record.fields.len();
                if num_fields > 0 {
                    self.src.push_str("let ");
                    self.src.push_str("{ ");
                    for (i, field) in record.fields.iter().enumerate() {
                        let name = to_grain_ident(&field.name);
                        let arg = format!("{}{}", name, tmp);
                        self.src.push_str(&name);
                        self.src.push_str(": ");
                        self.src.push_str(&arg);
                        if i < num_fields - 1 {
                            self.src.push_str(", ");
                        }
                        results.push(arg);
                    }
                    self.src.push_str(" }: ");
                    self.src.push_str(&self.typename_lower(resolve, *ty));
                    self.src.push_str(" = ");
                    self.src.push_str(op);
                    self.src.push_str("\n");
                }
            }
            Instruction::RecordLift { ty, record, .. } => {
                if operands.len() > 0 {
                    let mut result = String::new();
                    result.push_str("{ ");
                    let num_fields = record.fields.len();
                    for ((i, field), val) in record.fields.iter().enumerate().zip(operands) {
                        result.push_str(&to_grain_ident(&field.name));
                        result.push_str(": ");
                        result.push_str(&val);
                        if i < num_fields - 1 {
                            result.push_str(", ");
                        }
                    }
                    result.push_str(" }");
                    results.push(result);
                } else {
                    results.push("void".to_string())
                }
            }

            Instruction::TupleLower { ty, tuple, .. } => {
                let tmp = self.locals.tmp("tuple");
                let length = tuple.types.len();
                if length == 0 {
                    return;
                }
                if length == 1 {
                    results.push(operands[0].clone());
                    return;
                }
                self.src.push_str("let (");
                for i in 0..length {
                    let arg = format!("t{}_{}", tmp, i);
                    self.src.push_str(&arg);
                    if i < length - 1 {
                        self.src.push_str(", ");
                    }
                    results.push(arg);
                }
                if length == 1 {
                    self.src.push_str(",")
                }
                self.src.push_str(") = ");
                self.src.push_str(&operands[0]);
                self.src.push_str("\n");
            }
            Instruction::TupleLift { ty, tuple, .. } => {
                if operands.len() == 0 {
                    results.push("void".to_string());
                } else {
                    results.push(format!("({})", operands.join(", ")));
                }
            }

            Instruction::HandleLower { handle, ty, .. } => {
                results.push(format!(
                    "WasmI32.load(WasmI32.fromGrain({}.handle), 4n)",
                    operands.pop().unwrap(),
                ))
            },

            Instruction::HandleLift { handle, ty, name } => {
                let (is_own, resource) = match handle {
                    Handle::Borrow(resource) => (false, resource),
                    Handle::Own(resource) => (true, resource),
                };
                if self.interface.is_exported_resource(*resource) {
                    self.src.push_str(&format!("Memory.incRef({})\n", operands[0]));
                    results.push(format!("WasmI32.toGrain({})", operands[0]));
                } else {
                    let tmp = self.locals.tmp("handle_lift");
                    self.src.push_str(&format!(
                        "let {} = {{handle: WasmI32.toGrain(DataStructures.newInt32({})),}}: ",
                        tmp,
                        operands.pop().unwrap()
                    ));
                    self.src.push_str(&self.typename_lift(resolve, *resource));
                    self.src.push_str("\n");
                    results.push(tmp);
                }
            },

            // TODO: checked
            Instruction::FlagsLower { flags, ty, .. } => match flags_repr(flags) {
                Int::U8 | Int::U16 => results.push(format!(
                    "WasmI32.(>>>)(WasmI32.fromGrain({}), 8n)",
                    operands.pop().unwrap()
                )),
                Int::U32 => results.push(format!(
                    "WasmI32.load(WasmI32.fromGrain({}), 4n)",
                    operands.pop().unwrap()
                )),
                Int::U64 => {
                    let tmp = self.locals.tmp("flags");
                    uwriteln!(
                        self.src,
                        "let {tmp} = WasmI64.load(WasmI32.fromGrain({}), 8n)",
                        operands[0]
                    );
                    results.push(format!("WasmI32.wrapI64({tmp})"));
                    results.push(format!("WasmI32.wrapI64(WasmI64.shrU({tmp}, 32n))"));
                }
            },

            Instruction::FlagsLift { flags, ty, .. } => match flags_repr(flags) {
                Int::U8 => results.push(format!(
                "WasmI32.toGrain(WasmI32.(|)(WasmI32.(<<)({}, 8n), WasmI32.fromGrain(0us))): Uint8",
                operands[0]
            )),
                Int::U16 => results.push(format!(
                "WasmI32.toGrain(WasmI32.(|)(WasmI32.(<<)({}, 8n), WasmI32.fromGrain(0uS))): Uint16",
                operands[0]
            )),
                Int::U32 => results.push(format!(
                    "WasmI32.toGrain(DataStructures.newUint32({})): Uint32",
                    operands[0]
                )),
                Int::U64 => {
                    let op0 = &operands[0];
                    let op1 = &operands[1];
                    results.push(format!("WasmI32.toGrain(DataStructures.newUint64(WasmI64.or(WasmI64.extendI32U({op0})), WasmI64.shl({op1}, 32N))))): Uint64"));
                }
            },

            Instruction::VariantPayloadName => {
                results.push("e".to_string());
            }

            Instruction::VariantLower {
                variant,
                results: result_types,
                ..
            } => {
                let blocks = self
                    .blocks
                    .drain(self.blocks.len() - variant.cases.len()..)
                    .collect::<Vec<_>>();
                // let payloads = self
                //     .payloads
                //     .drain(self.payloads.len() - variant.cases.len()..)
                //     .collect::<Vec<_>>();

                let mut result_operand = String::new();

                let tmp = self.locals.tmp("variant_lower");
                for (i, ty) in result_types.iter().enumerate() {
                    results.push(format!("result{}_{}", tmp, i));
                    let initial_value = wasm_zero(*ty);
                    result_operand.push_str(&format!(
                        "let mut {} = {}\n",
                        format!("result{}_{}", tmp, i),
                        initial_value
                    ))
                }
                result_operand.push_str("match (");
                result_operand.push_str(&operands[0]);
                result_operand.push_str(") {\n");
                for (case, (block, block_operands)) in variant.cases.iter().zip(blocks) {
                    result_operand.push_str(&case_name(&case.name));
                    if case.ty.is_some() {
                        result_operand.push_str("(e)")
                    }
                    result_operand.push_str(" => {\n");
                    result_operand.push_str(&block);
                    for (i, op) in block_operands.iter().enumerate() {
                        result_operand.push_str(&format!(
                            "{} = {}\n",
                            format!("result{}_{}", tmp, i),
                            op
                        ))
                    }
                    result_operand.push_str("},\n");
                }
                result_operand.push_str("}\n");
                self.src.push_str(&result_operand);
            }

            Instruction::VariantLift { variant, ty, .. } => {
                let blocks = self
                    .blocks
                    .drain(self.blocks.len() - variant.cases.len()..)
                    .collect::<Vec<_>>();

                // let ty = self.gen.type_string(&Type::Id(*ty));
                let mut result = format!("match (");
                result.push_str(&operands[0]);
                result.push_str(") {\n");
                for (i, (case, block)) in variant.cases.iter().zip(blocks).enumerate() {
                    if i == variant.cases.len() - 1 {
                        result.push_str("_");
                    } else {
                        result.push_str(&i.to_string());
                        result.push_str(&"n");
                    }
                    result.push_str(" => {\n");
                    let (block, ops) = block;
                    result.push_str(&block);
                    let args = &ops.join(", ");
                    let case_name = case.name.to_upper_camel_case();
                    result.push_str(&case_name);
                    // result.push_str("::");
                    // result.push_str(&case_name(&case.name));
                    if !case.ty.is_none() {
                        result.push_str("(");
                        result.push_str(args);
                        result.push_str(")");
                    }
                    result.push_str("\n},\n");
                }
                result.push_str("}");
                results.push(result);
            }

            Instruction::OptionLower {
                results: result_types,
                payload,
                ..
            } => {
                let tmp = self.locals.tmp("option_lower");

                let (mut some, some_operands) = self.blocks.pop().unwrap();
                let (mut none, none_operands) = self.blocks.pop().unwrap();
                for (i, op) in some_operands.iter().enumerate() {
                    some.push_str(&format!("{} = {}\n", format!("result{}_{}", tmp, i), op))
                }
                for (i, op) in none_operands.iter().enumerate() {
                    none.push_str(&format!("{} = {}\n", format!("result{}_{}", tmp, i), op))
                }

                let mut result_operand = String::new();
                for (i, ty) in result_types.iter().enumerate() {
                    results.push(format!("result{}_{}", tmp, i));
                    let initial_value = wasm_zero(*ty);
                    result_operand.push_str(&format!(
                        "let mut {} = {}\n",
                        format!("result{}_{}", tmp, i),
                        initial_value
                    ))
                }
                let operand = &operands[0];
                result_operand.push_str(&format!(
                    "match ({operand}) {{
                        Some(e) => {{
                            {some}}},
                        None => {{
                            {none}}},
                    }}\n"
                ));
                self.src.push_str(&result_operand);
            }

            Instruction::OptionLift { payload, ty, .. } => {
                let (some, some_operands) = self.blocks.pop().unwrap();
                let _ = self.blocks.pop().unwrap();
                let args = &some_operands.join(", ");
                let operand = &operands[0];
                results.push(format!(
                    "match ({operand}) {{
                        0n => None,
                        1n => {{
                            {some}
                            Some({args})
                        }},
                        _ => fail \"invalid enum discriminant\",
                    }}"
                ));
            }

            Instruction::ResultLower {
                results: result_types,
                result,
                ..
            } => {
                let tmp = self.locals.tmp("result_lower");

                let (mut err, err_operands) = self.blocks.pop().unwrap();
                let (mut ok, ok_operands) = self.blocks.pop().unwrap();
                for (i, op) in err_operands.iter().enumerate() {
                    err.push_str(&format!("{} = {}\n", format!("result{}_{}", tmp, i), op))
                }
                for (i, op) in ok_operands.iter().enumerate() {
                    ok.push_str(&format!("{} = {}\n", format!("result{}_{}", tmp, i), op))
                }

                let mut result_operand = String::new();
                for (i, ty) in result_types.iter().enumerate() {
                    results.push(format!("result{}_{}", tmp, i));
                    let initial_value = wasm_zero(*ty);
                    result_operand.push_str(&format!(
                        "let mut {} = {}\n",
                        format!("result{}_{}", tmp, i),
                        initial_value
                    ))
                }
                let operand = &operands[0];
                result_operand.push_str(&format!(
                    "match ({operand}) {{
                        Ok(e) => {{
                            {ok}
                        }},
                        Err(e) => {{
                            {err}
                        }},
                    }}\n"
                ));
                self.src.push_str(&result_operand);
            }

            Instruction::ResultLift { result, ty, .. } => {
                let (err, err_operands) = self.blocks.pop().unwrap();
                let (ok, ok_operands) = self.blocks.pop().unwrap();
                let err_args = if err_operands.len() < 1 { 
                    "void".to_string() 
                } else { 
                    err_operands.join(", ") 
                };
                let ok_args = if ok_operands.len() < 1 { 
                    "void".to_string()
                } else {
                     ok_operands.join(", ")
                };
                let operand = &operands[0];
                results.push(format!(
                    "match ({operand}) {{
                        0n => {{
                            {ok}
                            Ok({ok_args})
                        }},
                        1n => {{
                            {err}
                            Err({err_args})
                        }},
                        _ => fail \"invalid enum discriminant\",
                    }}"
                ));
            }

            Instruction::EnumLower { enum_, ty, .. } => {
                self.enum_lower(resolve, *ty, &enum_, &operands[0], results)
            }
            Instruction::EnumLift { enum_, ty, .. } => {
                let mut result = format!("match (");
                result.push_str(&operands[0]);
                result.push_str(") {\n");
                for (i, case) in enum_.cases.iter().enumerate() {
                    if i == enum_.cases.len() - 1 {
                        result.push_str("_");
                    } else {
                        result.push_str(&i.to_string());
                        result.push_str(&"n");
                    }
                    result.push_str(" => {\n");
                    self.enum_lift_case(resolve, *ty, case, &mut result);
                    result.push_str("\n},\n");
                }
                result.push_str("}");
                results.push(result);
            }

            Instruction::ListCanonLower { .. } | Instruction::StringLower { .. } => {
                let tmp = self.locals.tmp("list_canon_lower");
                let val = format!("vec_{}", tmp);
                let ptr = format!("ptr_{}", tmp);
                let len = format!("len_{}", tmp);
                self.push_str(&format!("let {} = {}\n", val, operands[0]));
                self.push_str(&format!(
                    "let {} = WasmI32.(+)(WasmI32.fromGrain({}), 8n)\n",
                    ptr, val
                ));
                self.push_str(&format!(
                    "let {} = WasmI32.load(WasmI32.fromGrain({}), 4n)\n",
                    len, val
                ));
                results.push(ptr);
                results.push(len);
            }
            Instruction::ListCanonLift { element, .. } => {
                let tmp = self.locals.tmp("list_canon_lift");
                let len = format!("len_{}", tmp);
                self.push_str(&format!("let {} = {}\n", len, operands[1]));
                match element {
                    Type::Char => {
                        self.push_str(&format!(
                            "let str_{} = DataStructures.allocateString({})\n",
                            tmp, len
                        ));
                        self.push_str(&format!(
                            "Memory.copy(WasmI32.(+)(str_{}, 8n), {}, {})\n",
                            tmp, operands[0], len
                        ));
                        self.push_str(&format!(
                            "let str_{0} = WasmI32.toGrain(str_{0}): String\n",
                            tmp
                        ));
                        results.push(format!("str_{}", tmp));
                    }
                    _ => {
                        self.push_str(&format!(
                            "let bytes_{} = DataStructures.allocateBytes({})\n",
                            tmp, len
                        ));
                        self.push_str(&format!(
                            "Memory.copy(WasmI32.(+)(bytes_{}, 8n), {}, {})\n",
                            tmp, operands[0], len
                        ));
                        self.push_str(&format!(
                            "let bytes_{0} = WasmI32.toGrain(bytes_{0}): Bytes\n",
                            tmp
                        ));
                        results.push(format!("bytes_{}", tmp));
                    }
                }
            }
            Instruction::StringLift { .. } => {
                let tmp = self.locals.tmp("string_lift");
                let len = format!("len_{}", tmp);
                self.push_str(&format!("let {} = {}\n", len, operands[1]));
                self.push_str(&format!(
                    "let str_{} = DataStructures.allocateString({})\n",
                    tmp, len
                ));
                self.push_str(&format!(
                    "Memory.copy(WasmI32.(+)(str_{}, 8n), {}, {})\n",
                    tmp, operands[0], len
                ));
                self.push_str(&format!(
                    "let str_{0} = WasmI32.toGrain(str_{0}): String\n",
                    tmp
                ));
                results.push(format!("str_{}", tmp));
            }

            Instruction::ListLower {
                element, realloc, ..
            } => {
                let body = self.blocks.pop().unwrap();
                let tmp = self.locals.tmp("list_lower");
                let vec = format!("vec_{}", tmp);
                let result = format!("result_{}", tmp);
                let len = format!("len_{}", tmp);
                self.push_str(&format!("let {} = {}\n", vec, operands[0]));
                self.push_str(&format!(
                    "let {} = WasmI32.(>>>)(WasmI32.fromGrain(List.length({})), 1n)\n",
                    len, vec
                ));
                let size = self.interface.gen.sizes.size(element);
                self.push_str(&format!(
                    "let {} = Memory.malloc(WasmI32.(*)({}, {}n))\n",
                    result, len, size
                ));
                self.push_str(&format!("let mut list = vec_{}\n", tmp));
                self.push_str(&format!("let mut i = 0n\n"));
                self.push_str(&format!("while (true) {{\n",));
                self.push_str(&format!("match (list) {{\n",));
                self.push_str(&format!("[] => {{\n",));
                self.push_str(&format!("break\n",));
                self.push_str(&format!("}},\n",));
                self.push_str(&format!("[e, ...rest] => {{\n",));
                self.push_str(&format!("list = rest\n",));
                self.push_str(&format!(
                    "let base = WasmI32.(+)({}, WasmI32.(*)(i, {}n))\n",
                    result, size,
                ));
                self.push_str(&format!("i = WasmI32.(+)(i, 1n)\n"));
                let (body, _) = body;
                self.push_str(&body);
                self.push_str("}\n");
                self.push_str("}\n");
                self.push_str("}\n");
                results.push(format!("{}", result));
                results.push(len);

                // if realloc.is_none() {
                //     // If an allocator isn't requested then we must clean up the
                //     // allocation ourselves since our callee isn't taking
                //     // ownership.
                //     self.free_list.push(result);
                // }
            }

            Instruction::ListLift { element, ty, .. } => {
                let (body, body_ops) = self.blocks.pop().unwrap();
                let tmp = self.locals.tmp("list_lift");
                let size = self.interface.gen.sizes.size(element);
                let len = format!("len_{}", tmp);
                let base = format!("base_{}", tmp);
                let result = format!("result_{}", tmp);
                self.push_str(&format!("let {} = {}\n", base, operands[0]));
                self.push_str(&format!("let {} = {}\n", len, operands[1],));
                self.push_str(&format!("let mut {} = []\n", result));
                self.push_str(&format!("Memory.incRef(WasmI32.fromGrain({}))\n", result));

                self.push_str("for (let mut i = WasmI32.(-)(");
                self.push_str(&len);
                // We loop from the end of the list to the start,
                // because wasm is unsigned when we hit `0` we'll loop back around to `-1`
                // and exit the loop.
                self.push_str(", 1n); WasmI32.(!=)(i, -1n); i = WasmI32.(-)(i, 1n)) {\n");
                self.push_str("let base = WasmI32.(+)(");
                self.push_str(&base);
                self.push_str(", WasmI32.(*)(i, ");
                self.push_str(&size.to_string());
                self.push_str("n))\n");
                self.push_str(&body);
                self.push_str(&result);
                self.push_str(" = [");
                self.push_str(&body_ops[0]);
                self.push_str(", ...");
                self.push_str(&result);
                self.push_str("]\n");
                self.push_str("}\n");
                results.push(result);
            }
            Instruction::IterElem { .. } => results.push("e".to_string()),
            Instruction::IterBasePointer => results.push("base".to_string()),

            Instruction::CallWasm { name, sig, .. } => {
                assert!(sig.results.len() < 2);
                if sig.results.len() > 0 {
                    self.push_str("let ret = ");
                    results.push("ret".to_string());
                }
                self.push_str("wit_bindgen_");
                self.push_str(&to_grain_ident(name));
                self.push_str("(");
                self.push_str(&operands.join(", "));
                self.push_str(")\n");
            }

            Instruction::CallInterface { func } => {
                self.let_results(func.results.len(), results);
                let mut result_operand = String::new();
                let iface_name = if let Some(id) = self.interface.interface {
                    resolve.interfaces[id]
                        .name
                        .as_ref()
                        .unwrap()
                        .to_upper_camel_case()
                } else {
                    "".to_string()
                };
                match &func.kind {
                    FunctionKind::Freestanding => {
                        result_operand.push_str(&format!(
                            "{iface_name}Exports.{n}",
                            n = to_grain_ident(&func.name),
                        ));
                    }
                    FunctionKind::Static(ty)
                    | FunctionKind::Method(ty)
                    | FunctionKind::Constructor(ty) => {
                        result_operand.push_str(&format!(
                            "{iface_name}Exports.{r}.{}",
                            &to_grain_ident(func.item_name()),
                            r = (resolve.types[*ty]
                                .name
                                .as_deref()
                                .unwrap()
                                .to_upper_camel_case()),
                        ));
                    }
                }
                result_operand.push_str("(");
                result_operand.push_str(&operands.join(", "));
                result_operand.push_str(")\n");

                self.push_str(&result_operand);
            }
            // Instruction::Return { .. } if self.interface.gen.in_import => match self.sig.ret.scalar
            // {
            //     None => {
            //         for op in operands.iter() {
            //             self.store_in_retptr(op);
            //         }
            //     }
            //     Some(Scalar::Void) => {
            //         assert!(operands.is_empty());
            //     }
            //     Some(Scalar::Type(_)) => {
            //         assert_eq!(operands.len(), 1);
            //         self.src.push_str("return ");
            //         self.src.push_str(&operands[0]);
            //         self.src.push_str(";\n");
            //     }
            //     Some(Scalar::OptionBool(o)) => {
            //         assert_eq!(operands.len(), 1);
            //         let variant = &operands[0];
            //         if !is_empty_type(self.gen.resolve, &o) {
            //             self.store_in_retptr(&format!("{}.val", variant));
            //         }
            //         self.src.push_str("return ");
            //         self.src.push_str(&variant);
            //         self.src.push_str(".is_some;\n");
            //     }
            //     Some(Scalar::ResultBool(ok, err)) => {
            //         assert_eq!(operands.len(), 1);
            //         let variant = &operands[0];
            //         assert!(self.sig.retptrs.len() <= 2);
            //         uwriteln!(self.src, "if (!{}.is_err) {{", variant);
            //         if ok.is_some() {
            //             if get_nonempty_type(self.gen.resolve, ok.as_ref()).is_some() {
            //                 self.store_in_retptr(&format!("{}.val.ok", variant));
            //             } else {
            //                 self.empty_return_value();
            //             }
            //         }
            //         uwriteln!(
            //             self.src,
            //             "   return 1;
            //                 }} else {{"
            //         );
            //         if err.is_some() {
            //             if get_nonempty_type(self.gen.resolve, err.as_ref()).is_some() {
            //                 self.store_in_retptr(&format!("{}.val.err", variant));
            //             } else {
            //                 self.empty_return_value();
            //             }
            //         }
            //         uwriteln!(
            //             self.src,
            //             "   return 0;
            //                 }}"
            //         );
            //         assert_eq!(self.ret_store_cnt, self.sig.retptrs.len());
            //     }
            // },
            Instruction::Return { amt, .. } => {
                assert!(*amt <= 1);
                // if self.needs_cleanup_list {
                //     self.push_str("while (WasmI32.ne(cleanupList, 0n)) {\n");
                //     self.push_str("let (ptr, restCleanup) = WasmI32.toGrain(cleanupList): (WasmI32, WasmI32)\n");
                //     self.push_str("Memory.free(ptr)\n");
                //     self.push_str("Memory.free(cleanupList)\n");
                //     self.push_str("cleanupList = restCleanup\n");
                //     self.push_str("}\n");
                // }
                match amt {
                    0 => self.push_str("void\n"),
                    1 => {
                        self.push_str(&operands[0]);
                        self.push_str("\n");
                    }
                    _ => {
                        self.push_str("(");
                        self.push_str(&operands.join(", "));
                        self.push_str(")\n");
                    }
                }
            }

            Instruction::I32Load { offset } => {
                results.push(format!("WasmI32.load({}, {}n)", operands[0], offset));
            }
            Instruction::I32Load8U { offset } => {
                results.push(format!("WasmI32.load8U({}, {}n)", operands[0], offset));
            }
            Instruction::I32Load8S { offset } => {
                results.push(format!("WasmI32.load8S({}, {}n)", operands[0], offset));
            }
            Instruction::I32Load16U { offset } => {
                results.push(format!("WasmI32.load16U({}, {}n)", operands[0], offset));
            }
            Instruction::I32Load16S { offset } => {
                results.push(format!("WasmI32.load16S({}, {}n)", operands[0], offset));
            }
            Instruction::I64Load { offset } => {
                results.push(format!("WasmI64.load({}, {}n)", operands[0], offset));
            }
            Instruction::F32Load { offset } => {
                results.push(format!("WasmF32.load({}, {}n)", operands[0], offset));
            }
            Instruction::F64Load { offset } => {
                results.push(format!("WasmF64.load({}, {}n)", operands[0], offset));
            }
            Instruction::LengthLoad { offset } => {
                results.push(format!("WasmI32.load({}, {}n)", operands[0], offset));
            }
            Instruction::PointerLoad { offset } => {
                results.push(format!("WasmI32.load({}, {}n)", operands[0], offset));
            }
            Instruction::I32Store { offset } => {
                self.push_str(&format!(
                    "WasmI32.store({}, {}, {}n)\n",
                    operands[1], operands[0], offset
                ));
            }
            Instruction::I32Store8 { offset } => {
                self.push_str(&format!(
                    "WasmI32.store8({}, {}, {}n)\n",
                    operands[1], operands[0], offset
                ));
            }
            Instruction::I32Store16 { offset } => {
                self.push_str(&format!(
                    "WasmI32.store16({}, {}, {}n)\n",
                    operands[1], operands[0], offset
                ));
            }
            Instruction::I64Store { offset } => {
                self.push_str(&format!(
                    "WasmI64.store({}, {}, {}n)\n",
                    operands[1], operands[0], offset
                ));
            }
            Instruction::F32Store { offset } => {
                self.push_str(&format!(
                    "WasmF32.store({}, {}, {}n)\n",
                    operands[1], operands[0], offset
                ));
            }
            Instruction::F64Store { offset } => {
                self.push_str(&format!(
                    "WasmF64.store({}, {}, {}n)\n",
                    operands[1], operands[0], offset
                ));
            }
            Instruction::LengthStore { offset } => {
                self.push_str(&format!(
                    "WasmI32.store({}, {}, {}n)\n",
                    operands[1], operands[0], offset
                ));
            }
            Instruction::PointerStore { offset } => {
                self.push_str(&format!(
                    "WasmI32.store({}, {}, {}n)\n",
                    operands[1], operands[0], offset
                ));
            }

            Instruction::GuestDeallocate { .. } => {
                uwriteln!(self.src, "free((void*) ({}));", operands[0]);
            }
            Instruction::GuestDeallocateString => {
                uwriteln!(self.src, "if (({}) > 0) {{", operands[1]);
                uwriteln!(self.src, "free((void*) ({}));", operands[0]);
                uwriteln!(self.src, "}}");
            }
            Instruction::GuestDeallocateVariant { blocks } => {
                let blocks = self
                    .blocks
                    .drain(self.blocks.len() - blocks..)
                    .collect::<Vec<_>>();

                uwriteln!(self.src, "switch ((int32_t) {}) {{", operands[0]);
                for (i, (block, results)) in blocks.into_iter().enumerate() {
                    assert!(results.is_empty());
                    uwriteln!(self.src, "case {}: {{", i);
                    self.src.push_str(&block);
                    self.src.push_str("break;\n}\n");
                }
                self.src.push_str("}\n");
            }
            Instruction::GuestDeallocateList { element } => {
                let (body, results) = self.blocks.pop().unwrap();
                assert!(results.is_empty());
                let ptr = self.locals.tmp("ptr");
                let len = self.locals.tmp("len");
                uwriteln!(self.src, "int32_t {ptr} = {};", operands[0]);
                uwriteln!(self.src, "int32_t {len} = {};", operands[1]);
                let i = self.locals.tmp("i");
                uwriteln!(self.src, "for (int32_t {i} = 0; {i} < {len}; {i}++) {{");
                let size = self.interface.gen.sizes.size(element);
                uwriteln!(self.src, "int32_t base = {ptr} + {i} * {size};");
                uwriteln!(self.src, "(void) base;");
                uwrite!(self.src, "{body}");
                uwriteln!(self.src, "}}");
                uwriteln!(self.src, "if ({len} > 0) {{");
                uwriteln!(self.src, "free((void*) ({ptr}));");
                uwriteln!(self.src, "}}");
            }

            i => unimplemented!("{:?}", i),
        }
    }
}

pub fn is_empty_type(resolve: &Resolve, ty: &Type) -> bool {
    let id = match ty {
        Type::Id(id) => *id,
        _ => return false,
    };
    match &resolve.types[id].kind {
        TypeDefKind::Type(t) => is_empty_type(resolve, t),
        TypeDefKind::Record(r) => r.fields.is_empty(),
        TypeDefKind::Tuple(t) => t.types.is_empty(),
        _ => false,
    }
}

pub fn wasm_zero(ty: WasmType) -> &'static str {
    match ty {
        WasmType::I32 => "0n",
        WasmType::I64 => "0N",
        WasmType::F32 => "0.0w",
        WasmType::F64 => "0.0W",
        WasmType::Pointer => "0n",
        WasmType::Length => "0n",
        WasmType::PointerOrI64 => "0N",
    }
}

pub fn wasm_type(ty: WasmType) -> &'static str {
    match ty {
        WasmType::I32 => "WasmI32",
        WasmType::I64 => "WasmI64",
        WasmType::F32 => "WasmF32",
        WasmType::F64 => "WasmF64",
        WasmType::Pointer => "WasmI32",
        WasmType::Length => "WasmI32",
        WasmType::PointerOrI64 => "WasmI64",
    }
}

fn int_repr(repr: Int) -> &'static str {
    match repr {
        Int::U8 => "Uint8",
        Int::U16 => "Uint16",
        Int::U32 => "Uint32",
        Int::U64 => "Uint64",
    }
}

fn flags_repr(f: &Flags) -> Int {
    match f.repr() {
        FlagsRepr::U8 => Int::U8,
        FlagsRepr::U16 => Int::U16,
        FlagsRepr::U32(1) => Int::U32,
        FlagsRepr::U32(2) => Int::U64,
        repr => panic!("unimplemented flags {:?}", repr),
    }
}

fn int_suffix(repr: Int) -> &'static str {
    match repr {
        Int::U8 => "us",
        Int::U16 => "uS",
        Int::U32 => "ul",
        Int::U64 => "uL",
    }
}

fn bitcast(casts: &[Bitcast], operands: &[String], results: &mut Vec<String>) {
    for (cast, operand) in casts.iter().zip(operands) {
        results.push(perform_cast(operand, cast));
    }
}

fn perform_cast(operand: &str, cast: &Bitcast) -> String {
    match cast {
        Bitcast::None => operand.to_string(),
        Bitcast::I32ToI64 => format!("WasmI64.extendI32S({})", operand),
        Bitcast::F32ToI32 => format!("WasmI32.reinterpretF32({})", operand),
        Bitcast::F64ToI64 => format!("WasmI64.reinterpretF64({})", operand),
        Bitcast::I64ToI32 => format!("WasmI32.wrapI64({})", operand),
        Bitcast::I32ToF32 => format!("WasmF32.reinterpretI32({})", operand),
        Bitcast::I64ToF64 => format!("WasmF64.reinterpretI64({})", operand),
        Bitcast::F32ToI64 => {
            format!("WasmI64.reinterpretF64(WasmF64.promoteF32({}))", operand)
        }
        Bitcast::I64ToF32 => {
            format!("WasmF32.reinterpretI32(WasmI32.wrapI64({}))", operand)
        }
        Bitcast::P64ToI64 |
        Bitcast::I64ToP64 => operand.to_string(),
        Bitcast::P64ToP => format!("WasmI32.wrapI64({})", operand),
        Bitcast::PToP64 => format!("WasmI64.extendI32U({})", operand),
        Bitcast::I32ToP |
        Bitcast::PToI32 |
        Bitcast::PToL |
        Bitcast::LToP |
        Bitcast::I32ToL |
        Bitcast::LToI32 |
        Bitcast::I64ToL |
        Bitcast::LToI64 => operand.to_string(),
        Bitcast::Sequence(sequence) => {
            let [first, second] = &**sequence;
            perform_cast(&perform_cast(operand, first), second)
        }
    }
}

pub fn case_name(id: &str) -> String {
    if id.chars().next().unwrap().is_alphabetic() {
        id.to_upper_camel_case()
    } else {
        format!("V{}", id)
    }
}

fn to_grain_ident(name: &str) -> String {
    match name {
        "assert" => "assert_".into(),
        "break" => "break_".into(),
        "continue" => "continue_".into(),
        "else" => "else_".into(),
        "enum" => "enum_".into(),
        "except" => "except_".into(),
        "exception" => "exception_".into(),
        "fail" => "fail_".into(),
        "false" => "false_".into(),
        "for" => "for_".into(),
        "foreign" => "foreign_".into(),
        "from" => "from_".into(),
        "if" => "if_".into(),
        "include" => "include_".into(),
        "provide" => "provide_".into(),
        "let" => "let_".into(),
        "match" => "match_".into(),
        "mut" => "mut_".into(),
        "primitive" => "primitive_".into(),
        "rec" => "rec_".into(),
        "record" => "record_".into(),
        "throw" => "throw_".into(),
        "true" => "true_".into(),
        "type" => "type_".into(),
        "void" => "void_".into(),
        "wasm" => "wasm_".into(),
        "when" => "when_".into(),
        "while" => "while_".into(),
        s => s.to_lower_camel_case()
            .replace('.', "_")
            .replace(':', "_"),
    }
}
