(*CS 225 Final Project Imperative Objects 

Created by: Tim Stevens, Jonah Shechtman, and Brett Stine


The following program is a partial implementation of Featherweight Java with some slight changes. 
If you would like to run the program and have downloaded all the other files. Type make fj into your command line.
5/7/2018
 *)
open Util
open StringSetMap

exception TODO
exception METHOD_ERROR
exception TYPE_ERROR
exception FIELD_ERROR
exception CLASS_ERROR of string
exception STUCK_ERROR

(* cname is the core 'type' of types so to speak. Every object has a type cname*)
type cname = string
[@@deriving show {with_path = false}]
(* function names *) 
type fname = string
[@@deriving show {with_path = false}]
(* method names *)
type mname = string
[@@deriving show {with_path = false}]
(* variable names *)
type var = string
[@@deriving show {with_path = false}]


(* terms can have the following forms. This implementation of FJ does not really use
Variables since we do not plan on writing programs that consist of more than one term  *)
type term =
        | Var of var
        | FldAccess of term * fname
        | MethodInvoke of term * mname * term list
        | ObjectCreation of cname * term list
        | Cast of cname * term
        | This
[@@deriving show {with_path = false}]

(* t_env only exists for inside of a method invocation since there are no variables or Thisses any where else *)
type t_env = cname string_map
[@@deriving show {with_path = false}]

type tlist = term list
[@@deriving show {with_path = false}]

(* since the FJ mantra is everything is an object, the only type of value is an object that has only values for arguments *)
type value = VObjectCreation of cname * value list
[@@deriving show {with_path = false}]


type fldlist = (cname * fname)  list
[@@deriving show {with_path = false}]


(* return type, method name, list of arguments, body *)
type method_decl = MethodDecl of cname * mname * fldlist * term
[@@deriving show {with_path = false}]

(* class name, super class name, list of fields, list of methods *)
type class_decl = ClassDecl of cname * cname * fldlist * method_decl list
[@@deriving show {with_path = false}]

(* keeps track of legal classes and how to manipulate them  *)
type class_env = class_decl list
[@@deriving show {with_path = false}]

(* type tclass = *)

(* helper function for appending two lists. This is not tail recursive *)
let rec append l1 l2 =
  match l1 with
  | h :: t -> h :: append t l2
  | [] -> l2

(* this allows the class environment to function as a lookup table for classes and class properties *)
let rec class_search (cenv: class_env) (c : cname) : class_decl = match cenv with
        | [] -> raise (CLASS_ERROR c)
        | cd::ce -> begin match cd with
                |ClassDecl(c1,c2,fl,ml) -> if c = c1 then cd else class_search ce c
        end

let rec super_look (cenv: class_env) (c0 : cname) : cname  = match class_search cenv c0 with
        |ClassDecl(c1,c2,_,_) -> c2

(* keeps track of the subtype relation *)
let rec is_subtype (cenv : class_env) (c0 : cname) (csuper : cname) : bool = let c1 = super_look cenv c0 in
        if c1 = csuper || csuper = c0 then true else
        if c1 = "object" then false  else
        is_subtype cenv c1 csuper

(* do not use this version  This returns the raw list of fields including fields of the superclass *)
let rec field_loo (cenv: class_env) (c : cname) : fldlist = match class_search cenv c with
            | ClassDecl(c1,c2,fl,_) -> if c2 = "object" then fl else append fl (field_loo cenv c2)

(* this self proclaimed good version of field look returns a list of fields where each field is unique and breaks if not*)
let rec field_look (cenv: class_env) (c : cname) : fldlist = let fl = field_loo cenv c in
        let rec uniq (fl : fldlist) (f : cname * fname) : bool = match fl with
            | [] -> true
            | f1::fl1 -> (not ((snd f) = (snd f1))) && (uniq fl1 f)
        in
        let rec is_uniq (fl: fldlist) : bool  = match fl with
            | [] -> true
            | f::fl1 -> (uniq fl1 f) && (is_uniq fl1)
        in
        if (is_uniq fl) then fl else raise FIELD_ERROR

(* Do not use this either. This search is a class has a method and throws an error if not *)
let rec meth_list_search (ml : method_decl list) (m : mname) : method_decl = match ml with
        | [] -> raise METHOD_ERROR
        | md::me -> begin match md with
            | MethodDecl(c,m0,f,t) -> if m = m0 then md else meth_list_search me m
        end

(* This catches the error thrown by the above method and searches the superclass for the method this structure means we are always
searching the lowest possible place where the method could be. This has been implemented this way to accomodate for overriding  *)
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


(* This is a duplicate of the method above but it returns the body and the arguments instead of argument types and return type *)
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

(*  this returns the value corresponding to a field given a list of both and raises an error if one is not found. *)
let rec val_of_fld (fl : fldlist) (f1 : fname) (vl : value list) : value = begin match fl, vl with
        | [],[] -> raise FIELD_ERROR
        | [], _ -> raise FIELD_ERROR
        | _ ,[] -> raise FIELD_ERROR
        | f::fl1, v::vl1 -> if snd f = f1 then v else
                val_of_fld fl1 f1 vl1
        end

(* returns a term when a term is needed instead of a value *)
let rec term_of_val (v0 : value) : term = match v0 with
  | VObjectCreation(c, el) ->
    let rec iter (vl: value list) : tlist = match vl with
      | [] -> []
      | v::vl' -> term_of_val(v)::iter vl'
    in ObjectCreation(c,iter el)


type result =
        | Val of value
        | Step of class_env * term
        | Stuck
[@@deriving show {with_path = false}]

(* this is an unfinished function inteded to perform the substitution of fields for variables in  method invocations *)
let rec subst (cenv:class_env ) (old : term) (noo : value) (t : term) : term =
  match t with
  | This -> This
  | FldAccess(t,f) -> FldAccess(subst cenv old noo t,f)
  | Cast(c,t') -> Cast(c,(subst cenv old noo t'))
  | ObjectCreation(c,tl) ->
    let rec iter (tl: tlist) : tlist = match tl with
      |[] -> []
      | t'::tl' -> (subst cenv old noo t')::(iter tl')
    in
    ObjectCreation(c,iter(tl))
  | MethodInvoke(t',m,tl) ->
  let rec iter (tl: tlist) : tlist = match tl with
    |[] -> []
    | t'::tl' -> (subst cenv old noo t')::(iter tl')
  in
  MethodInvoke((subst cenv old noo t'),m,(iter tl))
  | Var(t') -> raise TODO

(* this substitutes This with a value in method invocations *)
let rec sub_this (cenv:class_env ) (v: value ) (t : term) : term =
  match t with
  | This -> term_of_val v
  | FldAccess(t',f) -> FldAccess((sub_this cenv v t'),f)
  | Cast(c,t') -> Cast(c,(sub_this cenv v t'))
  | ObjectCreation(c,tl) ->
    let rec iter (tl: tlist) : tlist = match tl with
      |[] -> []
      | t'::tl' -> (sub_this cenv v t')::(iter tl')
    in
    ObjectCreation(c,iter(tl))
  | MethodInvoke(t',m,tl) ->
    let rec iter (tl: tlist) : tlist = match tl with
      |[] -> []
      | t'::tl' -> (sub_this cenv v t')::(iter tl')
    in
    MethodInvoke((sub_this cenv v t'),m,(iter tl))
  | Var(t') -> raise TODO

(* this function puts both of the substitution functions together and does substitution for entire lists  *)
let rec subst_l (cenv: class_env) (v : value) (old_list: fldlist) (noo_list : value list) (t: term) : term =
  match old_list, noo_list with
  | [],[] -> t
  | old::ol, noo::nl -> raise TODO
  | _,_ -> raise TYPE_ERROR

let rec step (cenv : class_env) (e0 : term) : result = match e0 with
(* [E-ProjNew] *)
        | FldAccess(e1,f1) -> begin match step cenv e1 with
                | Val(VObjectCreation(c',vlist')) -> Val(val_of_fld(field_look cenv c') f1 vlist')
                | Step(cenv, e') -> Step(cenv, FldAccess(e',f1))
                | Stuck -> Stuck
                end
(* [E-InvkNew] *)
        | MethodInvoke(e1,m,e2) -> begin match step cenv e1 with
            | Val(VObjectCreation(c',vlist')) -> begin match meth_body_look cenv c' m with
                | _ , t1 -> Step(cenv, t1)
              end
            | Step(cenv,e3) -> Step(cenv,MethodInvoke(e3, m, e2))
            | Stuck -> Stuck
                end
(* [E-NewArg] *)
        | ObjectCreation(c,el) -> begin match el with
            | [] -> Val(VObjectCreation(c, []))
            | _ -> let rec val_q (cenv : class_env) (explist : tlist) : bool =
                     match explist with
                     |[] -> true
                     | t:: tl -> begin match step cenv t with
                         | Val(x) -> (val_q cenv tl)
                         | _ -> false
                       end
              in
              let rec term_iter (cenv : class_env) (explist : tlist) : tlist =
                     begin match explist with
                     |[] -> []
                     | t::tl -> begin match step cenv t with
                       | Val(x) -> (term_of_val x)::(term_iter cenv tl)
                       | Step(cenv, x) -> x::(term_iter cenv tl)
                       | Stuck -> raise STUCK_ERROR
                       end
                  end
              in
              let rec val_iter (cenv : class_env) (explist : tlist) : value list =
                begin match explist with
                  |[] -> []
                  | t::tl -> begin match step cenv t with
                      | Val(x) -> x::(val_iter cenv tl)
                      | _ -> raise TYPE_ERROR
                    end
                end
              in if (val_q cenv el)
                 then Val(VObjectCreation(c,(val_iter cenv el)))
                 else Step(cenv,ObjectCreation(c,(term_iter cenv el)))
          end
        | _ -> raise TODO


let rec step_star (cname : class_env) (t : term) : term = match (step cname t) with
  | Val(v) -> term_of_val v
  | Step(c ,t') -> step_star c t'
  | Stuck -> t



(* the following function implements the term typing rules given a class environment and a type environment. *)
let rec type_term (tenv : t_env) (cenv : class_env) (e0 : term) : cname = begin match e0 with
        | FldAccess(e1,fl) -> let rec fld_find (flist : fldlist) (f: fname) : cname = begin match flist with
                                        | [] -> raise FIELD_ERROR
                                        | fd::fdl -> if (snd fd) = f then (fst fd) else fld_find fdl f
                                        end
                                        in fld_find (field_look cenv (type_term tenv cenv e1)) fl
        | MethodInvoke(e1,m,tl) -> let rec type_args (cenv: class_env) (ml : cname list) (tl : tlist) (c: cname) : cname = match ml, tl with
            | [], [] -> c
            | [], _ -> raise TYPE_ERROR
            | _, [] -> raise TYPE_ERROR
            | m::ml1, t::tl1 -> if not(is_subtype cenv m (type_term tenv cenv t)) then raise TYPE_ERROR else (type_args cenv ml1 tl1 c)

                in let mtl = meth_type_look cenv (type_term tenv cenv e1) m in
                type_args cenv (fst mtl) tl (snd mtl)
        | ObjectCreation(c,tl) -> let rec type_flds (cenv: class_env) (fl : fldlist) (tl : tlist) (c: cname) : cname = match fl, tl with
            | [], [] -> c
            | [], _ -> raise TYPE_ERROR
            | _, [] -> raise TYPE_ERROR
            | f::fl1, t::tl1 -> if not(is_subtype cenv (type_term tenv cenv t) (fst f)) then raise TYPE_ERROR else (type_flds cenv fl1 tl1 c)
        in type_flds cenv (field_look cenv c) tl c
        | Cast(c,t) -> c
        | Var(v) -> StringMap.find v tenv
        | This -> StringMap.find "this" tenv
        end

(* Types methods within classes given a class environment and a typing environment. Returns true if the method satisfies the typing conventions *)
let rec type_meth (tenv: t_env) (cenv : class_env) (cl : cname) (m : mname) : bool = let (ml, rt) = meth_type_look cenv cl m in
        let (fs, t) = meth_body_look cenv cl m in
        let rec type_list (cenv : class_env) (clist : cname list) : bool = match clist with
            | [] -> true
            | cn::cnl -> (is_subtype cenv cn cn) && (type_list cenv cnl)
        in let rec tenv_add (tenv: t_env) (cenv: class_env) (ml : cname list) (args: fname list) : t_env = match ml, args with
            |[], [] -> tenv
            |_, [] -> raise METHOD_ERROR
            |[], _ -> raise METHOD_ERROR
            | m::ml',arg::args' -> tenv_add (StringMap.add arg m tenv) cenv ml' args'
        in (type_list cenv ml) && is_subtype cenv rt (type_term (StringMap.add "this" cl (tenv_add tenv cenv ml fs)) cenv t)

(* Types classes within a class environment and returns true if the method satisfies the typing conentions *)
let rec type_class (tenv: t_env) (cenv : class_env) (cl : cname) : bool = let ClassDecl(c0,c1,fl,ml) = class_search cenv cl in
    let rec meth_iter (cenv: class_env) (cl: cname) (ml: method_decl list) = match ml with
            | [] -> true
            | md::ml' -> match md with MethodDecl(_,mn,_,_) -> (type_meth tenv cenv cl mn) && (meth_iter cenv cl ml')
    in meth_iter cenv cl ml

(* returns true if the whole class environment is well typed *)
let rec type_cenv (tenv: t_env) (cenv : class_env) (clist : class_env) : bool = match clist with
        | [] -> true
        | cd::cl -> match cd with ClassDecl(c0,_,_,_) -> type_class tenv cenv c0 && type_cenv tenv cenv cl



(* testing *)

type 'a test_result =
  | R of 'a
  | TypeError
  | FieldError
  | MethodError
  | ClassError of string
[@@deriving show {with_path = false}]

(* cheap adaptation of the old testing harness into working with a class environment since we may want to vary the testing environment per class *)
type test_pack = class_env * term
[@@deriving show {with_path = false}]

let type_testing (tp : test_pack) : cname test_result = let (cenv, t) = tp in
    try
        if type_cenv StringMap.empty cenv cenv then R(type_term StringMap.empty cenv t) else raise (CLASS_ERROR "env err")
    with
    | TYPE_ERROR -> TypeError
    | FIELD_ERROR -> FieldError
    | METHOD_ERROR -> MethodError
    | (CLASS_ERROR s) -> ClassError(s)

let enviro : class_env = [ClassDecl("A","object",[("B","thing")],[])
                         ;ClassDecl("B","object",[],[])
                         ;ClassDecl("C","A",[],[])
                         ;ClassDecl("D","object",[("B","thing")],[MethodDecl("B","thistest",[],FldAccess(This,"thing"))])
                         ;ClassDecl("E","D",[("B","thing")],[])
                         ;ClassDecl("F","C",[],[])
                         ;ClassDecl("G","D",[("C","snd")],[MethodDecl("A","args",[("B","thin")],ObjectCreation("A",[Var("thin")]))])
                          ]

(* The type tests test the following condtions in order
- simple type recover
- field access
- field access of a subtype
- subtype transitivity
- Method invocation
- duplicate field error throwing
- Multiple fields and nmultiple classes and variables
*)
let type_test_block : test_block =
    TestBlock("TYPING", [((enviro,ObjectCreation("B",[])),R("B"))
                        ;((enviro, FldAccess(ObjectCreation("A",[ObjectCreation("B",[])]),"thing")), R("B"))
                        ;((enviro,FldAccess(ObjectCreation("C",[ObjectCreation("B",[])]),"thing")),R("B"))
                        ;((enviro,FldAccess(ObjectCreation("F",[ObjectCreation("B",[])]),"thing")),R("B"))
                        ;((enviro,MethodInvoke(ObjectCreation("D",[ObjectCreation("B",[])]),"thistest",[])),R("B"))
                        ;((enviro,ObjectCreation("E",[ObjectCreation("B",[]);ObjectCreation("B",[])])),FieldError)
                        ;((enviro,MethodInvoke(ObjectCreation("G",[ObjectCreation("C",[ObjectCreation("B",[])]);ObjectCreation("B",[])]),"args",[ObjectCreation("B",[])])),R("A"))
                         ]
    ,type_testing
    ,(=)
    ,[%show : test_pack]
    ,[%show: cname test_result]
    )

(* Step Testing. Since I figured out the testing harness for typing, I figured I would set it up for you folks
 *
 *
 * step testing is the function that actually runs the step function. it is passed to the harness through the test block *)

let step_testing (tp : test_pack) : result test_result = let (cenv, t) = tp in
    try
        R(step cenv (step_star cenv t))
    with
    | TYPE_ERROR -> TypeError
    | FIELD_ERROR -> FieldError
    | METHOD_ERROR -> MethodError
    | (CLASS_ERROR s) -> ClassError(s)

(* this is the step test block it has the form of a constructed tuple with a name, (tests, expected results) list, evaluation function, evaluation criteria, test print function, and result print function. *)

let step_test_block : test_block = TestBlock("STEP"
                      ,[((enviro,ObjectCreation("B",[])),R(Val(VObjectCreation("B",[]))))
                      ;((enviro,FldAccess(ObjectCreation("C",[ObjectCreation("B",[])]),"thing")),R(Val(VObjectCreation("B",[]))))
                       ;((enviro,MethodInvoke(ObjectCreation("D",[ObjectCreation("B",[])]),"thistest",[])),R(Val(VObjectCreation("B",[]))))]
                ,step_testing
                , (=)
                ,[%show : test_pack]
                , [%show: result test_result])

(* This is where it all goes to the Util.ml *)
let _ = _SHOW_PASSED_TESTS := true ;
run_tests [type_test_block; step_test_block]
