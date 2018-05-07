open Util
open StringSetMap

(* The Assignment:
 * 
 * Fill in the `raise TODO` parts of the code:
 * - 22 cases in the `step` function
 * - 07 cases in the `scope_ok` function
 * - 08 cases in the `infer` function
 *
 * See the writeup for the specification for `step`, `scope_ok` and `infer`
 * functions that you must implement.
 *
 * Passing all of the tests does not guarantee 100%. You may want to write some
 * tests of your own.
 *
 * The last case of `infer` is for unpack expressions. In both the writeup and
 * code we define an alternative (and equivalent) rule [Unpack-Alt] which is
 * more suggestive of an implementation than the original rule [Unpack].
 *
 * If you ever need to compare two types for equality, use the function tequal,
 * and not (=). tequal will compare types for alpha-equivalence, e.g., ∀X.X and
 * ∀Y.Y are alpha equivalent, so tequal (∀Y.Y) (∀X.X) will return true, whereas
 * (∀Y.Y) = (∀X.X) using OCaml's (=) operation will return false.
 *
 * You may find the following functions helpful:
 *
 * The empty string set: 
 *   
 *   on paper: {}
 *   in OCaml: StringSet.empty
 *
 * The singleton string set:
 *
 *   on paper: {x}
 *   in OCaml: StringSet.singleton x
 *   or      : StringSet.of_list [x]
 *
 * String set union:
 *
 *   on paper: S₁ ∪ S₂
 *   in OCaml: StringSet.union s1 s2
 *
 * Removing from a string set:
 *
 *   on paper: S \ {x}
 *   in OCaml: StringSet.remove x s
 *
 * Testing membership in a string set:
 *
 *   on paper: x ∈ S
 *   in OCaml: StringSet.mem x s
 *
 * Analogously for maps:
 *
 *   on paper: {}
 *   in OCaml: StringMap.empty
 *
 *   on paper: {x ↦ τ}
 *   in OCaml: StringMap.singleton x t
 *
 *   on paper: Γ[x ↦ τ]
 *   in OCaml: StringMap.add x t g
 *
 *   on paper Γ(x) = τ
 *   in OCaml: StringMap.find x g = t
 *
 * Remember to always use OCaml's structural equality (=), and never use
 * physical equality (==).
 *)
exception TODO
exception SUBTYPE_ERROR
exception METHOD_ERROR
exception TYPE_ERROR
exception FIELD_ERROR


type cname = string
type fname = string
type mname = string

type var = string

type term =
        | Var of var
        | FldAccess of term * fname
        | MethodInvoke of term * mname * term list
        | ObjectCreation of cname * term list
        | Cast of cname * term

type tlist = term list

type value = VObjectCreation of cname * value list
        
type tenv = cname string_map

type fldlist = (cname * fname)  list


type method_decl = MethodDecl of cname * mname * fldlist * term 

type class_decl = ClassDecl of cname * cname * fldlist * method_decl list

type class_env = class_decl list

(* type tclass = *)

let rec append l1 l2 =
  match l1 with
  | h :: t -> h :: append t l2
  | [] -> l2

let rec class_search (cenv: class_env) (c : cname) : class_decl = match cenv with
        | [] -> raise SUBTYPE_ERROR
        | cd::ce -> begin match cd with
                |ClassDecl(c1,c2,fl,ml) -> if c = c1 then cd else class_search ce c
        end

let rec super_look (cenv: class_env) (c0 : cname) : cname  = match class_search cenv c0 with
        |ClassDecl(c1,c2,_,_) -> c2

let rec is_subtype (cenv : class_env) (c0 : cname) (csuper : cname) : bool = let c1 = super_look cenv c0 in
        if c1 = csuper then true else
        if c1 = "object" then false else
        is_subtype cenv c1 csuper

let rec field_loo (cenv: class_env) (c : cname) : fldlist = match class_search cenv c with
            | ClassDecl(c1,c2,fl,_) -> if c2 = "object" then fl else append fl (field_loo cenv c2)

let rec field_look (cenv: class_env) (c : cname) : fldlist = let fl = field_loo cenv c in
        let rec uniq (fl : fldlist) (f : cname * fname) : bool = match fl with
            | [] -> true
            | f1::fl1 -> (not ((snd f) = (snd f1))) && (uniq fl1 f)
        in
        let rec is_uniq (fl: fldlist) : bool  = match fl with
            | [] -> true
            | f::fl1 -> (uniq fl f) && (is_uniq fl1)
        in 
        if (is_uniq fl) then fl else raise AMBIGUOUS_FIELDS_ERROR 

let rec meth_list_search (ml : method_decl list) (m : mname) : method_decl = match ml with
        | [] -> raise METHOD_ERROR
        | md::me -> begin match md with
            | MethodDecl(c,m0,f,t) -> if m = m0 then md else meth_list_search me m
        end

let rec meth_type_look (cenv: class_env) (c : cname) (m : mname) : (cname list) * cname = match class_search cenv c with
         | ClassDecl(c1,c2,_,mlist) -> try 
             match meth_list_search mlist m with
             | MethodDecl(c0,m0,f,t) -> let rec fst_ext (fl : fldlist): fname list = begin match fl with
                                        | [] -> []
                                        | fn::fdl -> (fst fn)::(fst_ext fdl)
                                        end
                                        in
                                        ((fst_ext f),c0) 
         with METHOD_ERROR -> if c2 = "object" then raise METHOD_ERROR else meth_type_look cenv c2 m


let rec meth_body_look (cenv: class_env) (c : cname) (m : mname) : (fname list) * term = match class_search cenv c with
         | ClassDecl(c1,c2,_,mlist) -> try 
             match meth_list_search mlist m with
             | MethodDecl(c0,m0,f,t) -> let rec snd_ext (fl : fldlist): fname list = begin match fl with
                                        | [] -> []
                                        | fn::fdl -> (snd fn)::(snd_ext fdl)
                                        end
                                        in
                                        ((snd_ext f),t) 
         with METHOD_ERROR -> if c2 = "object" then raise METHOD_ERROR else meth_body_look cenv c2 m

let rec val_of_fld (fl : fldlist) (f1 : fname) (vl : value list) : value = begin match fl, vl with
        | [],[] -> raise FIELD_ERROR
        | [], _ -> raise FIELD_ERROR
        | _ ,[] -> raise FIELD_ERROR
        | f::fl1, v::vl1 -> if snd f = f1 then v else
                val_of_fld fl1, vl1
        end
  
type result =
        | Val of value
        | Step of class_env * term
        | Stuck
  
let rec step (cenv : class_env) (e0 : term) : result = match e0 with
        | FldAccess(e1,f1) -> begin match e1 with
                | VObjectCreation(c',vlist') -> val_of_fld (field_look cenv c') f1 vlist'
                | _ -> FldAccess(Step(cenv, e1), f1)
                end
        | MethodInvoke(e1,m,e2) -> begin match e1 with
                | VObjectCreation(c',vlist') -> raise TODO
                | _ -> MethodInvoke(Step(cenv, e2), m, t1)
                end
        | ObjectCreation(c,el) -> begin match e1 with
                | value list -> VObjectCreation(c, vlist')
                | _ -> ObjectCreation(c, Step(cenv, e1))
                end
        | [] -> Stuck  
        end

let rec type_flds (fl : fldlist) (tl : tlist) (c: cname) : cname = match fl, tl with
    | [], [] -> c
    | [], _ -> raise TYPE_ERROR
    | _, [] -> raise TYPE_ERROR
    | f::fl1, t::tl1 -> if not(is_subtype cenv (fst f) (type_term cenv t)) then raise TYPE_ERROR else type_flds fl1 tl1

let rec type_term (cenv : class_env) (e0 : term) : cname = begin match e0 with
        | FldAccess(e1,fl) -> let rec fld_find (flist : fldlist) (f: fname) : cname = begin match flist with
                                        | [] -> raise TYPE_ERROR
                                        | fd::fdl -> if (snd fd) = f then (fst fd) else fld_find fdl f
                                        end
                                        in fld_find (field_look cenv (type_term cenv e1)) fl
        | MethodInvoke(e1,m,tl) -> let mtl = meth_type_look cenv (type_term cenv e1) m in
                type_flds (fst mtl) tl (snd mtl)
        | ObjectCreation(c,tl) -> type_flds (field_look cenv c) tl c
        | Cast(c,t) -> c
        | Var(v) -> failwith "this one doesn't make sense"
        end

let rec type_meth (cenv : class_env) (cl : cname) (m : mname) : bool = let (ml, rt) = meth_type_look cenv cl m in
        let (fs, t) = meth_body_look cenv cl m in
        let rec type_list (cenv : class_env) (clist : cname list) : bool = match clist with
            | [] -> true
            | cn::cnl -> try (is_subtype cenv cn cn) && (type_list cenv cnl) with SUBTYPE_ERROR -> false
        in (type_list cenv ml) && is_subtype cenv rt (type_term cenv t)
        
let rec type_class (cenv : class_env) (cl : cname) : bool = let ClassDecl(c0,c1,fl,ml) = class_search cenv cl in
    let rec meth_iter (cenv: class_env) (cl: cname) (ml: method_decl list) = match ml with
            | [] -> true
            | md::ml' -> match md with MethodDecl(_,mn,_,_) -> (type_meth cenv cl mn) && (meth_iter cenv cl ml')
    in meth_iter cenv cl ml

