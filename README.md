
# **Getting familiar with term definitions (de Bruijn-indexed) in `Term.lean`**
Open `Term.lean`.

The way we encode lambda calculus in this project is by using [De Bruijn indices](https://en.wikipedia.org/wiki/De_Bruijn_index).
De Bruijn indices are a way to represent variables in lambda calculus without using variable names. Instead, variables are represented by their position relative to their binding lambda.

For example, the lambda term `λx. λy. x` can be represented using De Bruijn indices as `λ. λ. 1`. Here, `1` refers to the variable bound by the first lambda (counting from the innermost lambda outward).
Another example: `λx. λy. y x` becomes `λ. λ. 0 1`. Here, `0` refers to the variable bound by the second lambda, and `1` refers to the variable bound by the first lambda.


> _~~Question 1~~._ At the end of `Term.lean`, manually write a term representing the Church number `3` represented in this De Bruijn encoding.

# **Define a transformer that turns a `Syntax` into a `Term` in `Syntax.lean`**

While De Bruijn representation offers significant advantages for formal proofs (as we'll explore in the coming weeks), it's not particularly intuitive for reading and writing Lambda terms. Instead, we prefer to work with the more natural string-variable encoding of lambda calculus, then use a translation function to convert to the De Bruijn representation implemented in Term.lean.


Open `Syntax.lean`. Notice the difference between the `Syntax` inductive type with constructors for variables, lambdas, applications, and values and the one in `Term.lean`.
        - `s_var` represents a variable with a string name.
        - `s_lam` represents a lambda abstraction with a string name.
        - `s_app` represents an application of one syntax to another.
        - `s_value` represents a term value. 

> _~~Question 2~~:_ Implement the `lookupName` function to find variable indices in a context.
`lookupName` searches for a variable name in a list of strings and returns its index.


> _~~Question 3~~:_ Implement the `elaborate'` function to convert `Syntax` to `Term` using a context. `elaborate'` converts `Syntax` to `Term` by recursively processing the syntax and maintaining a context of variable names.
> Example: `elaborate (λ "s" => λ "z" => "z")` should produce the term for the church encoding of zero in De Bruijn representation.

Notice that this file defines the following at the end, this `succ` will be needed in the next section:
```
def zero : Term := elaborate (λ "s" => λ "z" => "z")
def succ : Term :=
  elaborate (λ "n" => λ "s" => λ "z" => "s"("n"("s")("z")))
def one : Term :=
  elaborate ({succ}({zero}))
```


# **Datatype exercises.**

Open `Reduce.lean`.

> _~~Question 4~~:_ Fill in the definition of `Reduce`.

The definition of `Reduce` should match the rules on the page 55 of the Week 3 slides (https://moodle.epfl.ch/pluginfile.php/3426630/mod_resource/content/3/week03.pdf).

> _~~Question 5~~:_ Like we did in Livecoding of week 2, define the reflexive transitive closure `ReduceMany` using the standard library and declare the transitive properties (so we can use `calc`). Prove the context theorems for `ReduceMany`: `reduce_many_abs`, `reduce_many_app1`, `reduce_many_app2` (similarly to the lifting of `context_if` to the reflexive transitive closure we did in the livecoding of week 2.)

Open `Datatypes.lean`.

> _~~Question 6~~:_ Fill in the definitions for `btrue`, `bfalse`, `or`, and `and`.

> _Question 7:_ State and prove that `not (and btrue bfalse) ~~>* btrue` (`boolean_expr_simple`)

> _Question 8:_ Define `iszero` and state and prove the expected lemma for it: `iszero zero` reduces to `btrue` (`iszero_zero`), `iszero (succ n)` reduces to `bfalse` (`iszero_succ`).

> _~~Question 9~~:_ Define `flist_nil`, `flist_cons` in the style of fold-left lists. Define `flist_isnil` and prove the expected theorems about it: `isnil nil` reduces to `btrue` (`flist_isnil_nil`) and `isnil (cons h t)` reduces to `bfalse` (`flist_isnil_cons`).

> _Optional_: Define `flist_head` and prove the theorem about it: `head (cons h t)` reduces to `h` (`flist_head_cons`).

# Curiosity Step (Optional, No questions): Examining `Parser.lean` and `NiceParser.lean`
Note: Only explore this if you're interested in Lean engineering.

Lean offers sophisticated parser extensibility features that allow you to create custom syntax for new term constructions.
At the conclusion of these two files, you'll find practical examples demonstrating Lean's flexible syntax extension capabilities. We've provided these examples to help you write Terms more directly, eliminating the need to work through `Syntax.lean` and providing even nicer surface syntax (eliminating the quotes).

