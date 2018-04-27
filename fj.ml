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

let rec super_look (cenv: class_env) (c0 : cname) : cname  = match cenv with
        | [] -> raise SUBTYPE_ERROR
        | cd::ce -> begin match cd with 
                |ClassDecl(c1,c2,_, _ ,_) -> if c0 = c1 then c2 else super_look ce c0
                end

let rec is_subtype (cenv : class_env) (c0 : cname) (csuper : cname) : bool = begin match csuper with
        | c0 -> true
        end


let rec step (cenv : class_env) (e0 : term) : term = raise TODO

let rec type_term (cenv : class_env) (e0 : term) : cname = raise TODO

let rec type_meth (cenv : class_env) (cl : cname) (m : mname) : bool = raise TODO

let rec type_class (cenv : class_env) (cl : cname) (m : mname) : bool = raise TODO

