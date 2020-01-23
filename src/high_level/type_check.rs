use std::collections::{HashMap,HashSet};
use crate::high_level::ast::*;

pub struct TypeError {
    pub pos: HPos,
    pub code: ErrorCode,
}

pub enum ErrorCode {
    FuncAlreadyDefined,
    UndefinedFunc,
    UndefinedVar,
    VarAlreadyDefined,
    UnexpectedStaleId,
    UnexpectedUnusedId,
    CannotUnifyTypes(String,String),
}

impl ErrorCode {
    fn at<T>(self, pos: HPos) -> Err<T,TypeError> {
        Err(TypeError{pos, code:self})
    }

struct FuncType {
    return_type: HType,
    args: Vec<HType>,
}

struct PartialFuncType {
    return_type: Option<HType>,
    args: Vec<Option<HType>>,

#[derive(Clone,Copy,Default)]
struct VarMap {
    types: Vec<(HVarName, HType)>
}

impl VarMap {
    fn get<'a>(&'a self, pos: HPos, x: &HVarName) -> Result<&'a HType, TypeError> {
        for (k,v) in &self.types {
            if k == x {
                return Ok(v);
            }
        }
        ErrorCode::UndefinedVar.at(pos)
    }
    fn with(self, pos: HPos, x: HVarName, t: HType) -> Result<Self, TypeError> {
        if self.get(pos, x).is_err() {
            let mut types = self.types.clone();
            types.push((x,t));
            Ok(VarMap{types})
        } else {
            ErrorCode::VarAlreadyDefined.at(pos)
        }
    }
}

#[derive(Clone,Copy,Debug)]
struct Unifiable {
    id:usize
}

enum UnifInfo {
    Unused,
    Const(String),
    Var,
}

impl UnifInfo {
    fn name(&self) -> String {
        match self {
            Unused => "(unused)",
            Const(x) => x.clone(),
            Var => "var"
        }
    }
    fn is_const(&self, pos: HPos) -> Result<(),TypeError> {
        match self {
            Unused => ErrorCode::UnexpectedUnusedId.at(pos),
            Const(_) => true,
            Var => false
        }
    }
    fn merge_from(&mut self, other: &mut UnifInfo, pos: HPos) -> Result<(),TypeError> {
        let x = UnifInfo::Unused;
        std::mem::swap(other, &mut x);

        if x.is_const(pos)? {
            std::mem::swap(self, &mut x);
        }

        if x.is_const(pos)? {
            // Cannot unify two constants
            return ErrorCode::CannotUnifyTypes(x.name(), self.name()).at(pos);
        }
    }
}

#[derive(Default)]
struct Unifier {
    offset: usize,
    vals: Vec<usize>,
    info: Vec<UniInfo>,
}

impl Unifier {
    /// We increase the offset here so that the next round of id's don't conflict with the last
    /// This means if we ever encounter a stale one, we can detect it.
    fn clear(&mut self) -> {
        self.offset += self.vals.len();
        self.vals.clear();
        self.info.clear();
    }
    fn fresh_constant(&mut self, name: String) -> Unifiable {
        let id = self.offset + self.vals.len();
        self.info.push(UnifInfo::Const(name)),
        self.vals.push(id);
        Unifiable{id}
    }
    fn fresh_var(&mut self) -> Unifiable {
        let id = self.offset + self.vals.len();
        self.info.push(UnifInfo::Var);
        self.vals.push(id);
        Unifiable{id}
    }
    fn eq(&self, a: Unifiable, b: Unifiable) -> Result<bool,TypeError> {
        if a.id < self.offset || b.id < self.offset {
            return Err(ErrorCode::UnexpectedStaleId.at(pos));
        }
        self.vals[a.id - self.offset] == self.vals[b.id - self.offset]
    }
    fn unify(&mut self, pos: HPos, a: Unifiable, b: Unifiable) -> Result<(),TypeError> {
        if a.id < self.offset || b.id < self.offset {
            return Err(ErrorCode::UnexpectedStaleId.at(pos));
        }
        let aval = self.vals[a.id - self.offset];
        let bval = self.vals[b.id - self.offset];
        if aval != bval {
            self.info[aval].merge_from(self.info[bval], pos)?;
            for x in self.vals.iter_mut() {
                if *x == bval {
                    *x = aval;
                }
            }
        }
    }
    fn any_vars(&self) -> Result<bool,TypeError> {
        for x in &self.vals {
            if !self.info[x].is_const()? {
                return true;
            }
        }
        false
    }
}

#[derive(Default)]
struct Defs {
    functions: HashMap<HFuncName,FuncType>,
    lemmas: HashSet<HLemmaName>,
    unifier: Unifier,
}

impl Defs {
    /// Return true if any additional types were added
    fn expr(&self, e: &HExpr, var_types: &VarMap) -> Result<bool, TypeError>
    {
        for arg in &e.args {
            self.expr(arg, var_types)?;
        }

        let pos = e.pos;

        match &e.name {
            HName::UserFunc(f) => {
                if let Some(ft) = self.functions.get(f) {
                    actual_type = Some(ft.return_type.clone());
                    expected_args = ft.args.map(|t|Some(t.clone()));
                } else if let Some(pft) = intro_types.get(f) {
                    actual_type = ft.return_type.clone();
                    expected_args = ft.args.clone();
                } else {
                    return ErrorCode::UndefinedFunc.at(pos);
                }
            }
            HName::UserVar(x) => {
                actual_type = Some(var_types.get(x)?);
                expected_args = vec![];
            }
            HName::Builtin(b) => {
                match b {
                    HBuiltin::Eq => {
                        actual_type = 
                    }
                }
            }
        }
    }

    fn definition(&mut self, d: &HItemDef) -> Result<(), TypeError> {
        let pos = d.pos;
        let mut intro_types = HashMap::new();
        
        for name in &d.names {
            if functions.contains_key(name) {
                return ErrorCode::FuncAlreadyDefined.at(pos);
            }
            intro_types.insert(name.clone(), None);
        }

        
    }
}

pub fn type_check(script: &mut HScript) -> Result<(), TypeError> {
    let mut defs = Defs::default();
    for item in script.items {
        match item {
            HItem::Def(d) => defs.definition(d)?,
            HItem::Lemma(lem) => defs.lemma(lem)?,
        }
    }
}
