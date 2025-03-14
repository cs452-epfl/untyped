import Fos.Term
import Fos.Syntax
import Fos.Reduce
-- Or one of the following, use the one you like best
-- import Fos.Parser
-- import Fos.NiceParser
namespace Fos

def btrue : Term :=
  -- λt. λf. t
  Term.t_abs (Term.t_abs (Term.t_var 1))

def bfalse : Term :=
  -- λt. λf. f
  Term.t_abs (Term.t_abs (Term.t_var 0))

def or : Term :=
  -- λb. λc. b tru c
  Term.t_abs (Term.t_abs (Term.t_app (Term.t_app (Term.t_var 1)
                                                 btrue)
                                     (Term.t_var 0)))
def and : Term :=
  -- λb. λc. b c fls
  Term.t_abs (Term.t_abs (Term.t_app (Term.t_app (Term.t_var 1)
                                                 (Term.t_var 0))
                                     bfalse))
def not : Term :=
  -- λb. b fls tru
  Term.t_abs (Term.t_app (Term.t_app (Term.t_var 0)
                                     bfalse)
                         btrue)

theorem boolean_expr_simple :
  Term.t_app not
             (Term.t_app (Term.t_app and
                                     btrue)
                         bfalse) ~~>* btrue := by
  -- This lemma is wrong.
  --have h0 : ∀ (t : Term), Term.t_app btrue t ~~>* Term.t_abs t := by

  have h1 : ∀ (t : Term), Term.t_app (Term.t_app btrue
                                                 t)
                                     bfalse ~~>* t := by
    intro t
    simp [btrue]

    apply Relation.ReflTransGen.head
    apply Reduce.e_appabs

  have h1 : Term.t_app and btrue ~~>* Term.t_abs (Term.t_app (Term.t_app btrue
                                                                          (Term.t_var 0))
                                                              bfalse) := by
    simp [and]
    apply Relation.ReflTransGen.single
    apply Reduce.e_appabs

  have h2 : Term.t_app (Term.t_app and
                                   btrue)
                       bfalse ~~>* bfalse := by
    apply Relation.ReflTransGen.trans
    apply reduce_many_app1 h1
    simp

    apply Relation.ReflTransGen.head
    apply Reduce.e_appabs
    simp [btrue]

    apply Relation.ReflTransGen.head
    apply Reduce.e_appabs
    sorry


  sorry

-- Arithmetic

def iszero :=
  -- λm. m (λx. fls) tru
  Term.t_abs (Term.t_app (Term.t_app (Term.t_var 0)
                                     (Term.t_abs bfalse))
                         btrue)
theorem iszero_zero : elaborate ({iszero}({zero})) ~~>* btrue := by
  simp [iszero, zero]
  -- (λm. m (λx. fls) tru) (λs. λz. z)
  apply Relation.ReflTransGen.head
  apply Reduce.e_appabs
  -- (λs. λz. z) (λx. fls) tru
  apply Relation.ReflTransGen.head
  apply Reduce.e_app1
  apply Reduce.e_appabs
  -- (λz. z) tru
  apply Relation.ReflTransGen.head
  apply Reduce.e_appabs
  -- tru
  simp [btrue]
  apply Relation.ReflTransGen.refl

theorem iszero_succ : elaborate (λ "n" => {iszero}({succ}("n"))) ~~>* elaborate (λ "n" => {bfalse}) := by
  simp [iszero, succ]
  -- λn. ( (λm. m (λx. fls) tru) (λn. λs. λz. s (n s z)) )
  apply Relation.ReflTransGen.head
  apply Reduce.e_abs
  apply Reduce.e_appabs
  -- λn. ( (λn. λs. λz. s (n s z)) (λx. fls) tru)
  apply Relation.ReflTransGen.head
  apply Reduce.e_abs
  apply Reduce.e_app1
  apply Reduce.e_appabs

-- Fold lists

def flist_nil :=
  -- λf. λz. z
  Term.t_abs (Term.t_abs (Term.t_var 0))

def flist_cons :=
  -- λh. λt. λf. λz. f h (t f z)
  -- A list is encoded as its own fold function.
  Term.t_abs (Term.t_abs (Term.t_abs (Term.t_abs (
    Term.t_app (Term.t_app
        (Term.t_var 1)
        (Term.t_var 3)
      )
      (Term.t_app (Term.t_app
          (Term.t_var 2)
          (Term.t_var 1)
        )
        (Term.t_var 0)
      )
  ))))
def flist_isnil :=
  -- λl. l (λh. λt. fls) tru
  Term.t_abs (Term.t_app (Term.t_app (Term.t_var 0)
                                     (Term.t_abs (Term.t_abs bfalse)))
                         btrue)

theorem flist_isnil_nil : elaborate ({flist_isnil}({flist_nil})) ~~>* btrue := by
  simp [flist_isnil, flist_nil]
  -- (λl. l (λh. λt. fls) tru) (λf. λz. z)
  apply Relation.ReflTransGen.head
  apply Reduce.e_appabs
  -- (λf. λz. z) (λh. λt. fls) tru
  apply Relation.ReflTransGen.head
  apply Reduce.e_app1
  apply Reduce.e_appabs
  -- (λz. z) tru
  apply Relation.ReflTransGen.head
  apply Reduce.e_appabs
  -- tru
  simp [btrue]
  apply Relation.ReflTransGen.refl

theorem flist_isnil_cons :
  elaborate (λ "h" => λ "t" => {flist_isnil}({flist_cons}("h")("t")))
  ~~>* elaborate (λ "h" => λ "t" => {bfalse}) := by
  -- λh. λt. flist_isnil (flist_cons h t)
  simp [flist_isnil, flist_cons]
  -- λh. λt. (λl. l (λh'. λt'. fls) tru) ( (λh". λt". λf. λz. f h" (t" f z)) h t)
  apply Relation.ReflTransGen.head
  apply Reduce.e_abs
  apply Reduce.e_abs
  apply Reduce.e_appabs
  -- λh. λt. ( ( (λh". λt". λf. λz. f h" (t" f z)) h t) (λh'. λt'. fls) tru)
  apply Relation.ReflTransGen.head
  apply Reduce.e_abs
  apply Reduce.e_abs
  apply Reduce.e_app1
  apply Reduce.e_app1
  apply Reduce.e_app1
  apply Reduce.e_appabs
  -- λh. λt. ( ( (λt". λf. λz. f h (t" f z)) t) (λh'. λt'. fls) tru)
  apply Relation.ReflTransGen.head
  apply Reduce.e_abs
  apply Reduce.e_abs
  apply Reduce.e_app1
  apply Reduce.e_app1
  apply Reduce.e_appabs
  -- λh. λt. ( (λf. λz. f h (t f z)) (λh'. λt'. fls) tru)
  apply Relation.ReflTransGen.head
  apply Reduce.e_abs
  apply Reduce.e_abs
  apply Reduce.e_app1
  apply Reduce.e_appabs
  -- λh. λt. ( (λz. (λh'. λt'. fls) h (t (λh'. λt'. fls) z)) tru)
  apply Relation.ReflTransGen.head
  apply Reduce.e_abs
  apply Reduce.e_abs
  apply Reduce.e_appabs
  -- λh. λt. ( (λh'. λt'. fls) h (t (λh'. λt'. fls) tru) )
  apply Relation.ReflTransGen.head
  apply Reduce.e_abs
  apply Reduce.e_abs
  apply Reduce.e_app1
  apply Reduce.e_appabs
  -- λh. λt. ( (λt'. fls) (t (λh'. λt'. fls) tru) )
  apply Relation.ReflTransGen.head
  apply Reduce.e_abs
  apply Reduce.e_abs
  apply Reduce.e_appabs
  -- λh. λt. fls
  simp [btrue]
  apply Relation.ReflTransGen.refl

def flist_head :=
  -- λl. l (λh. λt. h) dummy
  Term.t_abs (
    Term.t_app (Term.t_app
      (Term.t_var 0)
      (Term.t_abs (Term.t_abs (Term.t_var 1)))
    )
    btrue -- Dummy term
  )
theorem flist_head_cons : elaborate (λ "h" => λ "t" => {flist_head}({flist_cons}("h")("t"))) ~~>* elaborate (λ "h" => λ "t" => "h") := by
  -- λh. λt. flist_head (flist_cons h t)
  simp [flist_head, flist_cons]
  -- λh. λt. (λl. l (λh'. λt'. h') dummy) ( (λh". λt". λf. λz. f h" (t" f z)) h t)
  apply Relation.ReflTransGen.head
  apply Reduce.e_abs
  apply Reduce.e_abs
  apply Reduce.e_app2
  apply Reduce.e_app1
  apply Reduce.e_appabs
  -- λh. λt. (λl. l (λh'. λt'. h') dummy) ( (λt". λf. λz. f h (t" f z)) t)
  apply Relation.ReflTransGen.head
  apply Reduce.e_abs
  apply Reduce.e_abs
  apply Reduce.e_app2
  apply Reduce.e_appabs
  -- λh. λt. (λl. l (λh'. λt'. h') dummy) (λf. λz. f h (t f z))
  apply Relation.ReflTransGen.head
  apply Reduce.e_abs
  apply Reduce.e_abs
  apply Reduce.e_appabs
  -- λh. λt. ( (λf. λz. f h (t f z)) (λh'. λt'. h') dummy)
  apply Relation.ReflTransGen.head
  apply Reduce.e_abs
  apply Reduce.e_abs
  apply Reduce.e_app1
  apply Reduce.e_appabs
  -- λh. λt. ( (λz. (λh'. λt'. h') h (t (λh'. λt'. h') z)) dummy)
  apply Relation.ReflTransGen.head
  apply Reduce.e_abs
  apply Reduce.e_abs
  apply Reduce.e_appabs
  -- λh. λt. ( (λh'. λt'. h') h (t (λh'. λt'. h') dummy) )
  apply Relation.ReflTransGen.head
  apply Reduce.e_abs
  apply Reduce.e_abs
  apply Reduce.e_app1
  apply Reduce.e_appabs
  -- λh. λt. ( (λt'. h) (t (λh'. λt'. h') dummy) )
  apply Relation.ReflTransGen.head
  apply Reduce.e_abs
  apply Reduce.e_abs
  apply Reduce.e_appabs
  -- λh. λt. h
  apply Relation.ReflTransGen.refl

end Fos
