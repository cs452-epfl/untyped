namespace Fos

/-
Abstract syntax tree of the language.
-/
inductive Term : Type where
| t_var : Nat -> Term
| t_abs : Term -> Term
| t_app : Term -> Term -> Term

def Rename : Type := Nat -> Nat
def Subst : Type := Nat -> Term

def Rename.comp (f : Rename) (g : Rename) : Rename := fun x => g (f x)

def Rename.lift (f : Rename) : Rename
| 0 => 0
| n+1 => (f n)+1

def Term.rename (t : Term) (f : Rename) : Term :=
  match t with
  | t_var n => t_var (f n)
  | t_abs t => t_abs (t.rename f.lift)
  | t_app t1 t2 => t_app (t1.rename f) (t2.rename f)

def Subst.lift (s : Subst) : Subst
| 0 => .t_var 0
| n+1 => (s n).rename Nat.succ

def Term.subst (t : Term) (s : Subst) : Term :=
  match t with
  | t_var n => s n
  | t_abs t => t_abs (t.subst s.lift)
  | t_app t1 t2 => t_app (t1.subst s) (t2.subst s)

def Subst.subst_zero (t : Term) : Subst
| 0 => t
| n+1 => .t_var n

/-
Substitutes the zero-indexed variable with the given term.
-/
def Term.subst_zero (t : Term) (u : Term) : Term :=
  t.subst (Subst.subst_zero u)

/-
Notation for substitution.
-/
notation:70 t "[" u "]" => Term.subst_zero t u

namespace Example

def incr : Rename := fun n => n + 1

#reduce Rename.lift incr 1
#reduce Rename.lift (Rename.lift incr) 1

-- λs. λz. s (s (s z))
def three := Term.t_abs (Term.t_abs (Term.t_app (Term.t_var 1)
                                                (Term.t_app (Term.t_var 1)
                                                            (Term.t_app (Term.t_var 1)
                                                                        (Term.t_var 0)))))
end Example

end Fos
