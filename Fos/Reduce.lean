import Fos.Term
import Fos.Syntax
import Mathlib.Logic.Relation
namespace Fos

inductive Reduce : Term -> Term -> Prop
-- TODO: define the reduction relation
| e_appabs : ∀ (t12 t2 : Term), Reduce (Term.t_app (Term.t_abs t12) t2)
                                       (t12[t2])
| e_app1 : ∀ (t1 t1' t2 : Term), Reduce t1 t1' ->
                                 Reduce (Term.t_app t1 t2) (Term.t_app t1' t2)
| e_app2 : ∀ (t1 t2 t2': Term), Reduce t2 t2' ->
                                Reduce (Term.t_app t1 t2) (Term.t_app t1 t2')
| e_abs : ∀ (t t': Term), Reduce t t' ->
                          Reduce (Term.t_abs t) (Term.t_abs t')

notation:40 t " ~~> " t' => Reduce t t'

def ReduceMany : Term -> Term -> Prop :=
-- Define it with the standard library
  Relation.ReflTransGen Reduce

notation:40 t " ~~>* " t' => ReduceMany t t'

instance : Trans ReduceMany Reduce ReduceMany where
  trans :=
    fun rs r => Relation.ReflTransGen.tail rs r

instance : Trans ReduceMany ReduceMany ReduceMany where
  trans :=
    Relation.ReflTransGen.trans

instance : Trans Reduce ReduceMany ReduceMany where
  trans :=
    fun r rs => Relation.ReflTransGen.head r rs

instance : Trans Reduce Reduce ReduceMany where
  trans :=
    fun r r' => Relation.ReflTransGen.head r (Relation.ReflTransGen.single r')

-- Reduce.ctx_abs, but for ReduceMany
theorem reduce_many_abs : (t ~~>* t') -> (elaborate (λ "x" => {t}) ~~>* elaborate (λ "x" => {t'})) := by
    intro h
    induction h
    . simp
      exact Relation.ReflTransGen.refl
    . rename_i b c t2b b2c ih
      simp [*] at *
      apply Relation.ReflTransGen.trans
      exact ih
      apply Relation.ReflTransGen.single
      apply Reduce.e_abs b c
      exact b2c

-- Reduce.ctx_app1, but for ReduceMany
theorem reduce_many_app1 : (t ~~>* t') -> (elaborate ({t}({a})) ~~>* elaborate ({t'}({a}))) := by
    intro h
    induction h
    . simp
      exact Relation.ReflTransGen.refl
    . rename_i b c t2b b2c ih
      simp [*] at *
      apply Relation.ReflTransGen.trans
      exact ih
      apply Relation.ReflTransGen.single
      apply Reduce.e_app1 b c a
      exact b2c

-- Reduce.ctx_app2, but for ReduceMany
theorem reduce_many_app2 : (t ~~>* t') -> (elaborate ({a}({t})) ~~>* elaborate ({a}({t'}))) := by
    intro h
    induction h
    . simp
      exact Relation.ReflTransGen.refl
    . rename_i b c t2b b2c ih
      simp [*] at *
      apply Relation.ReflTransGen.trans
      exact ih
      apply Relation.ReflTransGen.single
      apply Reduce.e_app2 a b c
      exact b2c

end Fos
