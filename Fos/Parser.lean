import Fos.Term
import Lean
open Lean Syntax Elab Meta
namespace Fos

namespace Parser

declare_syntax_cat fos_term
declare_syntax_cat fos_atom

scoped syntax:max "#" num : fos_atom
scoped syntax:50 "λ." fos_term : fos_atom
scoped syntax:max "(" fos_term ")" : fos_atom
scoped syntax:max "{" term "}" : fos_atom
scoped syntax:60 fos_atom* : fos_term

def mkVarRef (n : Nat) : MetaM Expr :=
  mkAppM ``Term.t_var #[mkNatLit n]

partial def elabFosTerm : Syntax -> TermElabM Expr
| `(fos_atom| #$n:num) => mkVarRef n.getNat
| `(fos_atom| {$t:term}) => do
  let expectedType <- pure (mkConst ``Term)
  let expr <- Elab.Term.elabTerm t expectedType
  return expr
| `(fos_atom| λ.$t:fos_term) => do
  let expr <- elabFosTerm t
  mkAppM ``Term.t_abs #[expr]
| `(fos_atom| ($t:fos_term)) => elabFosTerm t
| `(fos_term| $atoms:fos_atom*) => do
  if atoms.size < 1 then
    throwError "Expected at least one atom"
  else
    let head := atoms[0]!
    let tail := atoms[1:]
    let mut result <- elabFosTerm head
    for atom in tail do
      let expr <- elabFosTerm atom
      result <- mkAppM ``Term.t_app #[result, expr]
    return result
| _ => throwUnsupportedSyntax

elab "```" term:fos_term "```" : term => elabFosTerm term

section Examples

#check ```#0```
#check ```λ.#0```
#check ```λ.λ.#0#1```

private def zero : Term := ```
λ.λ.#0
```

private def succ : Term := ```
λ.λ.λ.#1(#2#1#0)
```

private def one : Term := ```
{succ}{zero}
```

private def two : Term := ```
{succ}{one}
```

private def three : Term := ```
{succ}{two}
```

end Examples

end Parser

end Fos
