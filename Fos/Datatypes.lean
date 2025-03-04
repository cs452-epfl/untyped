import Fos.Term
import Fos.Syntax
import Fos.Reduce
-- Or one of the following, use the one you like best
-- import Fos.Parser
-- import Fos.NiceParser
namespace Fos

def btrue : Term :=
  sorry

def bfalse : Term :=
  sorry

def or : Term :=
  sorry

def and : Term :=
  sorry

def not : Term :=
  sorry

theorem boolean_expr_simple :=
  sorry

-- Arithmetic

def iszero :=
  sorry

theorem iszero_zero : elaborate ({iszero}({zero})) ~~>* btrue := by
  sorry

theorem iszero_succ : elaborate (λ "n" => {iszero}({succ}("n"))) ~~>* elaborate (λ "n" => {bfalse}) := by
  sorry

-- Fold lists

def flist_nil :=
  sorry

def flist_cons :=
  sorry

def flist_isnil :=
  sorry

theorem flist_isnil_nil : elaborate ({flist_isnil}({flist_nil})) ~~>* btrue := by
  sorry

theorem flist_isnil_cons :
  elaborate (λ "h" => λ "t" => {flist_isnil}({flist_cons}("h")("t")))
  ~~>* elaborate (λ "h" => λ "t" => {bfalse}) := by
  sorry

def flist_head :=
  sorry

theorem flist_head_cons : elaborate (λ "h" => λ "t" => {flist_head}({flist_cons}("h")("t"))) ~~>* elaborate (λ "h" => λ "t" => "h") := by
  sorry

end Fos
