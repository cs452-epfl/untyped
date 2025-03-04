import Fos.Term
import Fos.Syntax
import Mathlib.Logic.Relation
namespace Fos

inductive Reduce : Term -> Term -> Prop
-- TODO: define the reduction relation

notation:40 t " ~~> " t' => Reduce t t'

def ReduceMany : Term -> Term -> Prop :=
  sorry  -- Define it with the standard library

notation:40 t " ~~>* " t' => ReduceMany t t'

instance : Trans ReduceMany Reduce ReduceMany where
  trans :=
    sorry

instance : Trans ReduceMany ReduceMany ReduceMany where
  trans :=
    sorry

instance : Trans Reduce ReduceMany ReduceMany where
  trans :=
    sorry

instance : Trans Reduce Reduce ReduceMany where
  trans :=
    sorry

-- Reduce.ctx_abs, but for ReduceMany
theorem reduce_many_abs : (t ~~>* t') -> (elaborate (λ "x" => {t}) ~~>* elaborate (λ "x" => {t'})) := by
    sorry

-- Reduce.ctx_app1, but for ReduceMany
theorem reduce_many_app1 : (t ~~>* t') -> (elaborate ({t}({a})) ~~>* elaborate ({t'}({a}))) := by
    sorry

-- Reduce.ctx_app2, but for ReduceMany
theorem reduce_many_app2 : (t ~~>* t') -> (elaborate ({a}({t})) ~~>* elaborate ({a}({t'}))) := by
    sorry

end Fos
