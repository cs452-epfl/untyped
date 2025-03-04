import Fos.Term
import Lean
open Lean Syntax Elab Meta
namespace Fos
namespace NiceParser

declare_syntax_cat fos_term
declare_syntax_cat fos_atom

scoped syntax:max ident : fos_atom
scoped syntax:50 "λ" ident " -> " fos_term : fos_atom
scoped syntax:max "(" fos_term ")" : fos_atom
scoped syntax:max "{" term "}" : fos_atom
scoped syntax:60 fos_atom* : fos_term

def mkVarRef (n : Nat) : MetaM Expr :=
  mkAppM ``Term.t_var #[mkNatLit n]

abbrev Ctx := List String

def lookupName (n : String) : Ctx -> Option Nat
| [] => none
| x :: xs => if x = n then some 0 else
  match lookupName n xs with
  | some n => some (n + 1)
  | none => none

partial def elabFosTerm (ctx : Ctx) : Syntax -> TermElabM Expr
| `(fos_atom| $n:ident) => do
  match lookupName n.getId.toString ctx with
  | some n => mkVarRef n
  | none => throwError "Variable {n} not found"
| `(fos_atom | {$t:term}) => do
  let expectedType <- pure (mkConst ``Term)
  let expr <- Elab.Term.elabTerm t expectedType
  return expr
| `(fos_term | λ $n:ident -> $t:fos_term) => do
  let expr <- elabFosTerm (n.getId.toString :: ctx) t
  mkAppM ``Term.t_abs #[expr]
| `(fos_atom| ($t:fos_term)) => elabFosTerm ctx t
| `(fos_term| $atoms:fos_atom*) => do
  if atoms.size < 1 then
    throwError "Expected at least one atom"
  else
    let head := atoms[0]!
    let tail := atoms[1:]
    let mut result <- elabFosTerm ctx head
    for atom in tail do
      let expr <- elabFosTerm ctx atom
      result <- mkAppM ``Term.t_app #[result, expr]
    return result
| _ => throwUnsupportedSyntax

elab "```" term:fos_term "```" : term => elabFosTerm [] term

section Examples

#check ```λx -> x```
#check ```λx -> λy -> x y```
#check ```λx -> λy -> x(x y)```
#check ```λx -> λy -> x(y x)```

def zero : Term := ```
λs -> λz -> z
```

def succ : Term := ```
λn -> λs -> λz -> s(n s z)
```

#reduce succ

end Examples

end NiceParser
end Fos
