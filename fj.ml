open Util

exception TODO
exception METHOD_ERROR
exception TYPE_ERROR
exception FIELD_ERROR
exception CLASS_ERROR

type cname = string
[@@deriving show {with_path = false}]
type fname = string
[@@deriving show {with_path = false}]
type mname = string
[@@deriving show {with_path = false}]

type var = string
[@@deriving show {with_path = false}]

type term =
        | Var of var
        | FldAccess of term * fname
        | MethodInvoke of term * mname * term list
        | ObjectCreation of cname * term list
        | Cast of cname * term
[@@deriving show {with_path = false}]


type tlist = term list
[@@deriving show {with_path = false}]

type value = VObjectCreation of cname * value list
[@@deriving show {with_path = false}]
        

type fldlist = (cname * fname)  list
[@@deriving show {with_path = false}]


type method_decl = MethodDecl of cname * mname * fldlist * term 
[@@deriving show {with_path = false}]

type class_decl = ClassDecl of cname * cname * fldlist * method_decl list
[@@deriving show {with_path = false}]

type class_env = class_decl list
[@@deriving show {with_path = false}]

(* type tclass = *)

let rec append l1 l2 =
  match l1 with
  | h :: t -> h :: append t l2
  | [] -> l2

let rec class_search (cenv: class_env) (c : cname) : class_decl = match cenv with
        | [] -> raise TYPE_ERROR
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
        if (is_uniq fl) then fl else raise FIELD_ERROR 

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
(*
let rec step (cenv : class_env) (e0 : term) : term = match e0 with
        | FldAccess(e1,f1) -> begin match e1 with
                | VObjectCreation(c',vlist') -> begin match f1 with
                        | 
                end
        end
*)


let rec type_term (cenv : class_env) (e0 : term) : cname = begin match e0 with
        | FldAccess(e1,fl) -> let rec fld_find (flist : fldlist) (f: fname) : cname = begin match flist with
                                        | [] -> raise TYPE_ERROR
                                        | fd::fdl -> if (snd fd) = f then (fst fd) else fld_find fdl f
                                        end
                                        in fld_find (field_look cenv (type_term cenv e1)) fl
        | MethodInvoke(e1,m,tl) -> let rec type_flds (cenv: class_env) (ml : cname list) (tl : tlist) (c: cname) : cname = match ml, tl with
            | [], [] -> c
            | [], _ -> raise TYPE_ERROR
            | _, [] -> raise TYPE_ERROR
            | m::ml1, t::tl1 -> if not(is_subtype cenv m (type_term cenv t)) then raise TYPE_ERROR else (type_flds cenv ml1 tl1 c)

                in let mtl = meth_type_look cenv (type_term cenv e1) m in
                type_flds cenv (fst mtl) tl (snd mtl)
        | ObjectCreation(c,tl) -> let rec type_flds (cenv: class_env) (fl : fldlist) (tl : tlist) (c: cname) : cname = match fl, tl with
            | [], [] -> c
            | [], _ -> raise TYPE_ERROR
            | _, [] -> raise TYPE_ERROR
            | f::fl1, t::tl1 -> if not(is_subtype cenv (fst f) (type_term cenv t)) then raise TYPE_ERROR else (type_flds cenv fl1 tl1 c)
        in type_flds cenv (field_look cenv c) tl c
        | Cast(c,t) -> c
        | Var(v) -> failwith "this one doesn't make sense"
        end

let rec type_meth (cenv : class_env) (cl : cname) (m : mname) : bool = let (ml, rt) = meth_type_look cenv cl m in
        let (fs, t) = meth_body_look cenv cl m in
        let rec type_list (cenv : class_env) (clist : cname list) : bool = match clist with
            | [] -> true
            | cn::cnl -> try (is_subtype cenv cn cn) && (type_list cenv cnl) with TYPE_ERROR -> false
        in (type_list cenv ml) && is_subtype cenv rt (type_term cenv t)
        
let rec type_class (cenv : class_env) (cl : cname) : bool = let ClassDecl(c0,c1,fl,ml) = class_search cenv cl in
    let rec meth_iter (cenv: class_env) (cl: cname) (ml: method_decl list) = match ml with
            | [] -> true
            | md::ml' -> match md with MethodDecl(_,mn,_,_) -> (type_meth cenv cl mn) && (meth_iter cenv cl ml')
    in meth_iter cenv cl ml


let rec type_cenv (cenv : class_env) : bool = match cenv with
        | [] -> true
        | cd::cenv' -> match cd with ClassDecl(c0,_,_,_) -> type_class cenv c0 && type_cenv cenv'



(* testing *)

type 'a test_result =
  | R of 'a
  | TypeError
  | FieldError
  | MethodError
  | ClassError
[@@deriving show {with_path = false}]

type test_pack = class_env * term
[@@deriving show {with_path = false}]

let type_testing (tp : test_pack) : cname test_result = let (cenv, t) = tp in 
    try
        if type_cenv cenv then R(type_term cenv t) else raise CLASS_ERROR
    with
    | TYPE_ERROR -> TypeError
    | FIELD_ERROR -> FieldError
    | METHOD_ERROR -> MethodError
    | CLASS_ERROR -> ClassError

let enviro : class_env = [ClassDecl("A","object",[("object","thing")],[MethodDecl("B","Nothing",[],ObjectCreation("B",[]))]); ClassDecl("B","object",[],[])]
        
let type_test_block : test_block = 
    TestBlock("TYPING", [((enviro, FldAccess(ObjectCreation("A",[ObjectCreation("B",[])]),"thing")), R("B"))],type_testing,(=),[%show : test_pack],[%show: cname test_result])


let _ = _SHOW_PASSED_TESTS := true ;
run_tests [type_test_block]
