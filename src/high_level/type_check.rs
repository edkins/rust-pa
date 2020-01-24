use std::collections::{HashMap,HashSet};
use crate::high_level::ast::*;
use crate::high_level::semantics::FuncType;

#[derive(Debug)]
pub struct TypeError {
    pub pos: HPos,
    pub code: ErrorCode,
}

#[derive(Debug)]
pub enum ErrorCode {
    FuncAlreadyDefined,
    UndefinedFunc,
    UndefinedVar,
    VarAlreadyDefined,
    WrongArity,
    WrongType,
    TypeAnnotationWasWrong,
    ThingBeingDefinedIsNotMentioned,
    NotQuantifiedOverVar,
    WrongQuantifiedVars,
    LemmaAlreadyDefined,
    ClaimWithoutStatement,
    IdAlreadyUsed,
    BoxWithoutIntros,
    BoxWithoutContents,
    ClaimWithIntros,
    ClaimWithContents,
    BoxVarAlreadyUsed,
}

impl ErrorCode {
    fn at<T>(self, pos: HPos) -> Result<T,TypeError> {
        Err(TypeError{pos, code:self})
    }
}

#[derive(Clone,Default)]
struct VarMap {
    types: Vec<(HVarName, HType)>
}

impl VarMap {
    fn from_quants(pos: HPos, quants: &[HVarName]) -> Result<Self, TypeError> {
        let mut result = VarMap::default();
        for quant in quants {
            result.add(pos, quant.clone(), HType::Nat)?;
        }
        Ok(result)
    }
    fn get<'a>(&'a self, pos: HPos, x: &str) -> Result<&'a HType, TypeError> {
        for (k,v) in &self.types {
            if k == x {
                return Ok(v);
            }
        }
        ErrorCode::UndefinedVar.at(pos)
    }
    fn contains(&self, x: &str) -> bool {
        for (k,_) in &self.types {
            if k == x {
                return true;
            }
        }
        false
    }
    fn add(&mut self, pos: HPos, x: HVarName, t: HType) -> Result<(), TypeError> {
        if self.get(pos, &x).is_err() {
            self.types.push((x,t));
            Ok(())
        } else {
            ErrorCode::VarAlreadyDefined.at(pos)
        }
    }
    fn with(&self, pos: HPos, x: HVarName, t: HType) -> Result<Self, TypeError> {
        if self.get(pos, &x).is_err() {
            let mut types = self.types.clone();
            types.push((x,t));
            Ok(VarMap{types})
        } else {
            ErrorCode::VarAlreadyDefined.at(pos)
        }
    }
}

struct Defs {
    functions: HashMap<HFuncName,FuncType>,
    lemmas: HashSet<HLemmaName>,
}

impl Default for Defs {
    fn default() -> Self {
        Defs {
            functions: HashMap::<HFuncName,FuncType>::new(),
            lemmas: HashSet::new(),
        }
    }
}

impl Defs {
    fn get_arg_types(&self, pos: HPos, name: &HName) -> Result<Vec<HType>, TypeError> {
        match name {
            HName::UserFunc(f) => {
                if let Some(ft) = self.functions.get(f) {
                    Ok(ft.args.clone())
                } else {
                    ErrorCode::UndefinedFunc.at(pos)
                }
            }
            HName::Builtin(b) => {
                Ok(b.func_type().args)
            }
            HName::UserVar(_) | HName::Num(_) => Ok(vec![])
        }
    }

    fn get_func_type(&self, pos: HPos, name: &HName, var_types: &VarMap) -> Result<FuncType, TypeError> {
        match name {
            HName::UserFunc(f) => {
                if let Some(ft) = self.functions.get(f) {
                    Ok(ft.clone())
                } else {
                    ErrorCode::UndefinedFunc.at(pos)
                }
            }
            HName::UserVar(x) => {
                Ok(FuncType {
                    return_type: var_types.get(pos,x)?.clone(),
                    args: vec![]
                })
            }
            HName::Builtin(b) => {
                Ok(b.func_type())
            }
            HName::Num(_) => {
                Ok(FuncType {
                    return_type: HType::Nat,
                    args: vec![]
                })
            }
        }
    }

    fn take_remaining_name(name: &HName, remaining_names: &mut Vec<HFuncName>) -> Option<HFuncName> {
        if let HName::UserFunc(fname) = name {
            for i in 0..remaining_names.len() {
                if &remaining_names[i] == fname {
                    return Some(remaining_names.remove(i));
                }
            }
        }
        None
    }

    fn decide_defined_types(&mut self, e: &HExpr, expected_type: &HType, remaining_names: &mut Vec<HFuncName>) -> Result<(), TypeError> {
        let args;
        if let Some(fname) = Defs::take_remaining_name(&e.name, remaining_names) {
            args = vec![HType::Nat; e.args.len()];
            let ft = FuncType{
                return_type: expected_type.clone(),
                args: args.clone()
            };
            self.functions.insert(fname, ft);
        } else {
            args = self.get_arg_types(e.pos, &e.name)?
        }

        if e.args.len() != args.len() {
            return ErrorCode::WrongArity.at(e.pos);
        }

        for (i,arg) in e.args.iter().enumerate() {
            self.decide_defined_types(arg, &args[i], remaining_names)?;
        }
        Ok(())
    }

    fn expr(&self, e: &mut HExpr, var_types: &VarMap, expected_type: &HType) -> Result<(), TypeError>
    {
        let ft = self.get_func_type(e.pos, &e.name, var_types)?;
        if e.args.len() != ft.args.len() {
            return ErrorCode::WrongArity.at(e.pos);
        }

        if ft.return_type != *expected_type {
            return ErrorCode::WrongType.at(e.pos);
        }

        if e.typ == HType::Unchecked {
            e.typ = ft.return_type.clone();
        }
        
        if e.typ != ft.return_type {
            return ErrorCode::TypeAnnotationWasWrong.at(e.pos);
        }

        if e.name.is_quant() {
            let var_types2 = var_types.with(e.pos, get_quant_var(e)?.clone(), ft.args[0].clone())?;
            for (i,arg) in e.args.iter_mut().enumerate() {
                self.expr(arg, &var_types2, &ft.args[i])?;
            }
        } else {
            for (i,arg) in e.args.iter_mut().enumerate() {
                self.expr(arg, var_types, &ft.args[i])?;
            }
        };

        Ok(())
    }

    fn definition(&mut self, d: &mut HItemDef) -> Result<(), TypeError> {
        let pos = d.pos;
        
        // Check the names we're supposed to be defining
        for name in &d.names {
            if self.functions.contains_key(name) {
                return ErrorCode::FuncAlreadyDefined.at(pos);
            }
        }

        // Check the variables we're quantifying over
        let mut free_vars = vec![];
        let mut free_var_set = HashSet::new();
        for expr in &d.rules {
            get_free_vars(expr, &mut free_vars, &mut free_var_set)?;
        }
        match &d.quants {
            None => {
                d.quants = Some(free_vars);
            }
            Some(qs) => {
                free_vars.sort();
                let mut qs = qs.clone();
                qs.sort();
                if free_vars != qs {
                    return ErrorCode::WrongQuantifiedVars.at(pos);
                }
            }
        }

        // Decide whether we're defining predicates or functions
        let mut remaining_names = d.names.clone();
        for expr in &d.rules {
            self.decide_defined_types(expr, &HType::Bool, &mut remaining_names)?;
        }
        if !remaining_names.is_empty() {
            return ErrorCode::ThingBeingDefinedIsNotMentioned.at(pos);
        }

        // Typecheck the rules
        for expr in d.rules.iter_mut() {
            self.expr(expr, &VarMap::from_quants(pos, d.quants.as_ref().unwrap())?, &HType::Bool)?;
        }
        Ok(())
    }

    fn lemma(&mut self, lemma: &mut HItemLemma) -> Result<(), TypeError> {
        let pos = lemma.pos;
        if self.lemmas.contains(&lemma.name) {
            return ErrorCode::LemmaAlreadyDefined.at(pos);
        }

        self.expr(&mut lemma.statement, &VarMap::default(), &HType::Bool)?;
        let mut step_ids = HashSet::new();
        for step in lemma.proof.iter_mut() {
            self.step(step, &VarMap::default(), &mut step_ids)?;
        }
        Ok(())
    }
    
    fn step(&mut self, step: &mut HStep, vars: &VarMap, step_ids: &mut HashSet<HStepId>) -> Result<(), TypeError> {
        let pos = step.pos;

        // Deal with statement
        if let Some(stmt) = &mut step.statement {
            self.expr(stmt, vars, &HType::Bool)?;
        } else if !step.step_type.is_box() {
            return ErrorCode::ClaimWithoutStatement.at(pos);
        }

        // Deal with id
        if let Some(id) = step.id {
            if step_ids.contains(&id) {
                return ErrorCode::IdAlreadyUsed.at(pos);
            }
            step_ids.insert(id);
        }

        // Deal with intros and contents
        if step.step_type.is_box() {
            if step.intros.is_none() {
                return ErrorCode::BoxWithoutIntros.at(pos);
            }
            if step.contents.is_none() {
                return ErrorCode::BoxWithoutContents.at(pos);
            }

            // Deal with intros
            let mut v2 = vars.clone();
            for intro in step.intros.as_mut().unwrap().iter_mut() {
                match intro {
                    HIntro::Var(x) => {
                        if v2.contains(x) {
                            return ErrorCode::BoxVarAlreadyUsed.at(pos);
                        }
                        v2.add(pos, x.clone(), HType::Nat)?;
                    }
                    HIntro::Stmt(stmt,idopt) => {
                        if let Some(id) = idopt {
                            if step_ids.contains(id) {
                                return ErrorCode::IdAlreadyUsed.at(pos);
                            }
                            step_ids.insert(*id);
                        }
                        self.expr(stmt, &v2, &HType::Bool)?;
                    }
                }
            }

            // Deal with contents
            for content in step.contents.as_mut().unwrap() {
                self.step(content, &v2, step_ids)?;
            }
        } else {
            if step.intros.is_some() {
                return ErrorCode::ClaimWithIntros.at(pos);
            }
            if step.contents.is_some() {
                return ErrorCode::ClaimWithContents.at(pos);
            }
        }
        Ok(())
    }
}

fn get_quant_var(e: &HExpr) -> Result<&HVarName, TypeError> {
    if e.args.is_empty() {
        ErrorCode::WrongArity.at(e.pos)
    } else if let HName::UserVar(x) = &e.args[0].name {
        Ok(&x)
    } else {
        ErrorCode::NotQuantifiedOverVar.at(e.pos)
    }
}

/// Returns the free variables in the order in which they're encountered
///
/// Note this doesn't scale well for huge expressions with lots of vars and quantifiers
fn get_free_vars(e: &HExpr, result: &mut Vec<HVarName>, exclude: &mut HashSet<HVarName>) -> Result<(), TypeError> {
    if e.name.is_quant() {
        if e.args.is_empty() {
            return ErrorCode::WrongArity.at(e.pos);
        }
        let mut exclude2 = exclude.clone();
        exclude2.insert(get_quant_var(e)?.clone());
        for arg in &e.args[1..] {
            get_free_vars(arg, result, &mut exclude2)?;
        }
    } else if let HName::UserVar(x) = &e.name {
        if !e.args.is_empty() {
            return ErrorCode::WrongArity.at(e.pos);
        }
        if !exclude.contains(x) {
            result.push(x.clone());
            exclude.insert(x.clone());
        }
    } else {
        for arg in &e.args {
            get_free_vars(arg, result, exclude)?;
        }
    }
    Ok(())
}

pub fn type_check(script: &mut HScript) -> Result<(), TypeError> {
    let mut defs = Defs::default();
    for item in script.items.iter_mut() {
        match item {
            HItem::Def(d) => defs.definition(d)?,
            HItem::Lemma(lem) => defs.lemma(lem)?,
        }
    }
    Ok(())
}
