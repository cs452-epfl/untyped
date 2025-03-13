import Fos.Term
namespace Fos

/-
A easy-to-write syntax for the language with variables as strings.
-/
inductive Syntax where
| s_var : String -> Syntax
| s_lam : String -> Syntax -> Syntax
| s_app : Syntax -> Syntax -> Syntax
| s_value : Term -> Syntax

/-
A coercion from strings to the syntax, so that you can write `"x"` to mean `Syntax.s_var "x"`.
-/
instance : Coe String Syntax where
  coe s := Syntax.s_var s

notation "λ" n " => " t => Syntax.s_lam n t
notation t1 "(" t2 ")" => Syntax.s_app t1 t2
notation "{" t "}" => Syntax.s_value t

def lookupName (n : String) : List String -> Option Nat
-- Define the lookup function
| [] => none
| x :: xs => if x == n then some 0 else (lookupName n xs).map Nat.succ -- Use `map` for `Option` type

/-
Elaborate the `Syntax` to the debruijn-indexed `Term` given a context of variable names.
-/
@[simp]
def elaborate' (ctx : List String) : Syntax -> Term
| Syntax.s_var n => Term.t_var (lookupName n ctx).get!
| Syntax.s_lam n t =>
  Term.t_abs (elaborate' (n :: ctx) t)
| Syntax.s_app t1 t2 =>
  Term.t_app (elaborate' ctx t1) (elaborate' ctx t2)
| Syntax.s_value t =>
  t

@[simp]
def elaborate (s : Syntax) : Term :=
  elaborate' [] s

section Examples

def zero : Term := elaborate (λ "s" => λ "z" => "z")
def succ : Term :=
  elaborate (λ "n" => λ "s" => λ "z" => "s"("n"("s")("z")))
def one : Term :=
  elaborate ({succ}({zero}))

#reduce zero
#reduce succ
#reduce one

end Examples

end Fos
