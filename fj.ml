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

type value = 
        | VObjectCreation of cname * value list
        
type tenv = cname string_map


type fldlist = (cname * fname)  list

type ctor = ConstructorDecl of cname * fldlist * fldlist * tlist

type method_decl = MethodDecl of cname * mname * fldlist * tlist 

type class_decl = ClassDecl of cname * cname * fldlist  * ctor * method_decl list

type class_env = class_decl list

(* type tclass = *)

let rec append l1 l2 =
  match l1 with
  | h :: t -> h :: append t l2
  | [] -> l2

let rec class_search (cenv: class_env) (c : cname) : class_decl = match cenv with
        | [] -> raise SUBTYPE_ERROR
        | cd::ce -> begin match cd with
                |ClassDecl(c1,c2,fl,ctor,ml) -> if c = c1 then cd else class_search ce c
        end

let rec super_look (cenv: class_env) (c0 : cname) : cname  = match class_search cenv c0 with
        |ClassDecl(c1,c2,_, _ ,_) -> c2

let rec is_subtype (cenv : class_env) (c0 : cname) (csuper : cname) : bool = let c1 = super_look cenv c0 in
        if c1 = csuper then true else
        if c1 = c0 then false else
        is_subtype cenv c1 csuper

let rec field_look (cenv: class_env) (c : cname) : fldlist = match class_search cenv c with
            | ClassDecl(c1,c2,fl,_,_) -> if c = c2 then fl else append fl (field_look cenv c2)

let rec step (cenv : class_env) (e0 : term) : term = raise TODO

let rec type_term (cenv : class_env) (e0 : term) : cname = raise TODO

let rec type_meth (cenv : class_env) (cl : cname) (m : mname) : bool = raise TODO

let rec type_cons (cenv : class_env) (cl : cname) : bool = raise TODO

let rec type_class (cenv : class_env) (cl : cname) : bool = raise TODO

