require open Stdlib.FOL;
require open Stdlib.Prop;
require open Stdlib.Set;
require open Stdlib.Nat;
require open Stdlib.Bool;
require open Stdlib.Eq;
require open Stdlib.Z;
require open Stdlib.List;

// References used
// https://github.com/SMT-LIB/SMT-LIB.github.io/blob/2c5ae03b491c8c66e3570ad5f96940e585ee79c9/Version3/Core.smt3
// https://smtlib.cs.uiowa.edu/version3.shtml
// https://github.com/cvc5/alfc/blob/main/user_manual.md


// The core of SMT3 encoded in Lambdapi
// The symbol "->" will denote the function type constructor.
// It will be represented by the meta arrow "→".

// The notion of term, proposition and proof are not primitive in Lambdapi.
// As all expression in Lambdapi are called terms, we shall call these expression
// "object-terms", to distinguish them fron the other terms.
// Therefore, we create the type universe `Set'` (because `Set` already exist in `Stdlib.Set`, we define Set' just to illustrate)
// where user type will be encoded. Note that `Set` is a type and not a sort where Set is a sort in Coq.
symbol Set': TYPE;

// The El decoding function take a user term and return a term of type TYPE.
symbol El: Set' → TYPE;

// Similar definitions can be found in Stdlib.Set
print Set;
print τ; // ≃ El

// AletheLF define the type Quote of kind `(-> (! Type :var U) U Type)`.
// `Quote` could be translated into `τ`.

// The approach to encode the Prop,Set and TYPE universes in Lambdapi
// is more similar than the Tarski-style Universes encoding (fmi: https://www.cs.rhul.ac.uk/home/zhaohui/universes.pdf).


// The distinguished `Proof` type is a type whose kind is (-> Bool Type), where the argument of this type is the formula that is proven.
// In lambdapi, we create the type Prop that represent propsosition ≃ Bool of SMT.

// The Curry-de Bruijin-Howard correspondence leads to the introduction of an embedding `Prf` of propositions into types,
// mapping each proposition `A` to the type `Prf A` of its proofs. The propositions themselves are not the type of their proofs.
// If t is a proof of A, then it does not have the type A, but the type `Prf A`.
symbol Prop': TYPE;
injective symbol Prf: Prop' → TYPE; // The translate of (-> Bool Type).
// So (Proof (> x 0)) is translated into  Prf (x > 0)

// The stdlib.Prop defines
print Prop; // ≃ Prop'
print π; // ≃ Prf

// (assume S f)
// can be seen as syntax sugar for:
// (declare-const S (Proof f))
// that will be translated into:
symbol S (f: Prop): π f;

// # Dependent type
// In Version 3, functions that have a dependent type τ take as extra arguments also the types or value that τ depends on.
// (Forall (x A) B) or (Pi (x A) B) is translated into the meta term: Π (x : A), b x

// (declare-type BitVec ((! Int :var m :restrict (> m 0)))
symbol BitVec (m: ℤ) (p: π (0 < m)): TYPE;

type  BitVec; // Π m: ℤ, π (0 < m) → TYPE

// (declare-const div (→ Int (! Int :var n :restrict (distinct n 0)) Int)
symbol div (n: ℤ) (p: π (n ≠ 0)): TYPE;

// (declare-type Vector (Type (! Int :var m :restrict (>= m 0)))

symbol Vector (m: ℤ) (p: π (0 ≤ m)): TYPE;

//(define-type RVector ((n Int :restrict (> n 0))) (Vector Real n))
symbol RVector (n: ℤ) (p: π (0 < n)): TYPE;

// Proofs such as 0 < 8 can be proven automatically by
// rewriting rules (fmi. https://github.com/Deducteam/lambdapi-stdlib/blob/6559f043ef0c9cc4c5bf2af2e1707e11cd53debb/Z.lp#L356).
opaque symbol prf : π (0 < 8) ≔
begin
    simplify; apply top; 
end;

symbol BV8: BitVec 8 top; // so the proof is similar to construct ⊤ because rewriting rule reduces to ⊤.

//# Polymorphic type

// ## Parametric polymorphism
// Lambdapi support parametric polymorphism.
// The function `f` is defined for any `a b: Set`.
symbol h a b: τ a → τ b → τ b ≔ λ a b, b;

// ## Prenex predicative type quantification in types.
// For having the object-level polymorphism, we introduce a new constant `Scheme` into terms of type TYPE.
constant symbol Scheme: TYPE;
// Els embed the terms of type Scheme into terms of type TYPE
symbol Els: Scheme → TYPE;
// a constant `↑` to embed the terms of type `Set` into terms of type `Scheme` and a rule connecting these embeddings
symbol ↑: Set → Scheme;
rule Els (↑ $x) ↪ τ $x;
// We then introduce a quantifier for the variables of type `Set` in the terms of type `Scheme` and the associated rewriting rule
symbol forall: (Set → Scheme) → Scheme;
rule Els (forall $p) ↪ Π x: Set, Els ($p x);

symbol forallProp: (Set → Prop) → Prop;
rule π (forallProp $p) ↪ Π x: Set, π ($p x);


/*
# Module could be simulated with Lambdapi Module. Each module will need to have its own file.
Lambdapi does not support companion module (module in module).

(define-module M
   (
    (declare-type A ())    (declare-type B ())     (declare-type C ()) 
    (declare-const a A)    (declare-const b B)
    (declare-const f (→ A B))
    (declare-const g (→ B A)) 
    (define-const  h (→ A A) (lambda ((x A)) (g (f x))))
    (declare-const c (→ A C))
   )
   :types ( (A Type) (B Type) )
   :consts ( (a A) (f (→ A B)) (h (→ A A)) )
)
In the example above, only two of the type constructors and three of the constants are exported. 
Modifier `private` could prefix all symbol that are not in :types and :consts in a Lambdapi Module.


(declare-const a1 M1::A) ; declares a1 in the top-level namespace
(assert (= a1 M1::a))    ; adds this equality to the assertion context
(open M1)

(declare-const a1 M1::A) will be translate into `symbol a1: M1.A;`
(open M1) will be translate into `open M1;`
*/

/* # Inductive type
(define-inductive-types 
    ((Size ()) (BinTree ()) (Option (Type)) (List (Type)) (Pair (Type Type)))
    ( ; Size
      ( (small Size)
        (medium Size)
        (large Size)
      )
      ; BinTree
      ( (empty BinTree)
        (node (-> (! BinTree :selector left) (! BinTree :selector right) BinTree))
      )
      ; Option
      ( (none (→ (! Type :var A)   ; Type input is explicit for this constructor
                 (Option A)))    
        (some (→ (! Type :var A :implicit) 
                 (! A :selector val) (Option A)))
      )
      ; List
      ( (nil (→ (! Type :var E)    ; Type input is explicit
                (List E))) 
        (cons (→ (! Type :var E :implicit) 
                   (! E :selector head) (! (List E) :selector tail)) (List E))
      )
      ; Pair
      ( (pair (→ (! Type :var A :implicit) (! Type :var B :implicit) 
                 (A :selector first) (B :selector second) (Pair A B))))
      )
    )
  )

The command define-inductive-types takes two arguments:

1. a list of pairs of consisting of a type constructor (the name of the inductive type) and a possibly empty list of the form (Type ... Type)
    for each type constructor, indicating the number of type parameters it takes;
2. a corresponding list of value constructors for each inductive type.

The value constructors for an inductive type are themselves grouped in a list.
Each element of this list is a pair of a constructor and its type.
The type is given with the same syntax as any other (possibly functional) type.
An optional :selector attribute for one of the arguments of the constructor can be used to name the corresponding selector.

Several constraints on the type definition ensure the generality and the well-foundedness of the type.

* If a datatype D being defined has n parameters, each constructor of that datatype must return a value whose type has the form (D X₁ ... Xᵢ)
where X₁ ... Xᵢ are i distinct type variables. Consequently, the constructor must have those type variables as (implicit or explicit) input parameters.

* An inductive type can be parametrised by other types but not values. So it can be polymorphic but not dependent in general.

* If a datatype D being defined has n parameters, each constructor of that datatype must return a value whose type has the form (D X₁ ... Xᵢ)
where X₁ ... Xᵢ are i distinct type variables. Consequently, the constructor must have those type variables as (implicit or explicit) input parameters.
The constructors of the same datatype must have distinct names. However, the same name can be used for two constructors of distinct inductive types.

* An inductive type can be parametrised by other types but not values.
So it can be polymorphic but not dependent in general.
This is a temporary restriction that may be lifted at a later time.

* No nested types are allowed. That is, the type of a constructor's argument for an inductive type D cannot be a type term that nests D
within another type constructor. For instance, it is not possible to define a parametric inductive type (Tree A) with a constructor of type
(→ A (List (Tree A)) (Tree A)) or (→ A (Array Int (Tree A)) (Tree A)) because (Tree A) occurs nested in List (resp. Array).

* The same well-foundedness constraints as in 2.6 (which enable the type inhabited).
*/

/*
  Some Well-foundedness properties of SMTLIB3 inductive type might not be checked by Lambdapi type checker.
  The full support of inductive type is a work in progress in Lambdapi. 
*/

inductive Size: TYPE ≔
| small: Size
| medium: Size
| large: Size;

print 𝕃;

(A: Set) inductive Option: TYPE ≔
| None : Option A
| Some : τ A  → Option A;

print Option;


[A: Set] inductive Option2: TYPE ≔
| None2 : @Option2 A
| Some2 : τ A  → @Option2 A;

print Option2;


// Encoding Lemma/Rule of AletheLF

/*
; Equality  
  (declare-const = (-> (! Type :var A :implicit) 
                       A A Bool)
   :chainable 
   :builtin 
   "= denotes the identity function, which returns true iff 
    its two arguments are identical.")
*/
print =; // constant symbol = : Π [a: Set], τ a → τ a → Prop;

print Stdlib.Eq.=;

// (declare-const = (-> (! Type :var T :implicit) T T Bool))
// (declare-rule symm ((T Type) (t T) (s T))
//     :premises ((= t s))
//     :conclusion (= s t)
// )
opaque symbol eq_sym [T] [s t:τ T] : π(t = s) → π(s = t) ≔
begin
  assume a x y h; symmetry; apply h
end;

// # Right/Left associative with nil terminator

// (declare-const or (-> Bool Bool Bool) :right-assoc)
symbol or: Prop → Prop → Prop;
//notation or infix right 2;
rule or (or $x $y) $z ↪ or $x (or $y $z); // A rewrite rule is enough for normalizing automatically in right associative form.

// (declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
symbol ornil: Prop → Prop → Prop;
//notation ornil infix right 2;
// rule ornil $x ↪ (ornil) $x ⊥;  -- this does not preserved the type checking

// To do so, maybe we could propose another symbol `or-unary` that can rewrite to `or x false`
symbol or-unary: Prop → Prop;
rule or-unary $x ↪ or $x ⊥; 

// # Chainable
// (declare-const >= (-> Int Int Bool) :chainable)
// use list...

// Let's try to translate the rule:
// (declare-const concat (->
//   (! Int :var n :implicit)
//   (! Int :var m :implicit)
//   (BitVec n)
//   (BitVec m)
//   (BitVec (alf.add n m))))

symbol <_compat_< x y : π (0 < x ⇒ 0 < y ⇒ 0 < x + y) ≔
begin admit end;

symbol concat n m 
(p: π (0 < n)) (q: π (0 < m))
(b1: BitVec n p) (b2: BitVec m q): BitVec (n + m) (<_compat_< n m p q);


// (declare-fun x () (BitVec 2))
// (declare-fun y () (BitVec 3))
// (define-fun z () (BitVec 5) (concat x y))
symbol x: BitVec 2 top;
symbol y: BitVec 3 top;
symbol z : BitVec 5 (<_compat_< 2 3 top top) ≔ concat 2 3 top top x y;


// (declare-fun >= (Int Int) Bool)
// (declare-rule leq-contra ((x Int))
//     :premise ((>= x 0))
//     :requires (((alf.is_neg x) true))
//     :conclusion false)
symbol ≥:  ℤ → ℤ → Prop;
symbol leq-contra
    (x: ℤ)                  // ((x Int))
    (requires1: π (x < 0))  // :requires (((alf.is_neg x) true))  -- Something we need to verify ?
    : π (≥ x 0)             // :premise ((>= x 0)) -- Witness in a previous step
        → π ⊥;              // :conclusion false

// 2nd version
// (sig A P), or more suggestively {x:A | P x},
// denotes the subset of elements of the type A which satisfy the predicate P.
// In Coq it is defined as:s
// Inductive sig (A:Type) (P:A -> Prop) : Type :=
// exist : forall x:A, P x -> sig P.
// symbol sig: Set → (Set → Prop) → Set;
// symbol exist: Π (x : Set), 
(a:Set) (P: τ a → Prop) inductive sig: TYPE ≔
exist x : π (P x) → sig a P;

symbol π₁ s p : sig s p → τ s;
rule π₁ _ _ (exist $x $y) ↪ $x;

// Suggestion: use Subsets and Sigma-types for (x T) :requires P
// We have then the following definition
symbol leq-contra'
    (x-subset : sig int (λ (u: τ int), u > 0))      // ((x Int)) :requires (((alf.is_neg x) true))
    : π (≥ (π₁ _ _ x-subset) 0)                     // :premise ((>= x 0))
    → π ⊥;                                          // :conclusion false


// We overide the `=` symbol defined in Stdlib.Eq to simplify matters.  
constant symbol = [a] : τ a → τ a → Prop;

// # Match statements in ALF
// The ALF checker supports an operator alf.match for performing pattern matching on a target term. The syntax of this term is:
// (declare-rule symm ((F Bool))
//     :premises (F)
//     :conclusion
//         (alf.match ((t1 Int) (t2 Int)) F
//             (
//                 ((= t1 t2)       (= t2 t1))
//                 ((not (= t1 t2)) (not (= t2 t1)))
//             )
//         )
// )
//
// Pattern matching can be supported with rewriting rules
//
symbol symm (t1 t2: ℤ): Prop → Prop;
rule symm $x $y (= $x $y) ↪ = $x $y
with symm $x $y (¬ (= $x $y)) ↪ (¬ (= $y $x));

// To be able to consider Set terms as Prop we define:
constant symbol o : Set;
rule τ o ↪ Prop;


// We want now to translate:
//
// (program mk_trans ((t1 Int) (t2 Int) (t3 Int) (t4 Int) (tail Bool :list))
//     (Int Int Bool) Bool
//     (
//         ((mk_trans t1 t2 (and (= t3 t4) tail)) (alf.requires t2 t3 (mk_trans t1 t4 tail)))
//         ((mk_trans t1 t2 true)                 (= t1 t2))
//     )
// )
//
// (declare-rule trans (E Bool))
//     :premise-list E and
//     :conclusion
//         (alf.match ((t1 Int) (t2 Int) (tail Bool :list)) E
//         (
//             ((and (= t1 t2) tail) (mk_trans t1 t2 tail))
//         ))
// )


// When applying this rule, the formulas proven to this rule (say F1 ... Fn) will be collected
// and constructed as a single formula via the provided operator (and),
// and subsequently matched against the premise pattern F. In particular,
// in this case F is bound to (and F1 ... Fn). The conclusion of the rule returns F itself.
// Note that the type of functions provided as the second argument of :premise-list
// should be operators that are marked to take an arbitrary number of arguments,
// that is those marked e.g. with :right-assoc-nil or :chainable.
// The condition  :right-assoc-nil could not be check with Lambdapi, but :chainable comes for
// free with the type signature.
symbol premise-list : 𝕃 o → (Prop → Prop → Prop) → Prop;
rule premise-list ($x ⸬ $l) $op ↪ $op $x (premise-list $l $op)
with premise-list □ _ ↪ ⊤;
//NOTE: premise-list here take a list of Prop and not a list of Proof.
// We need to have a look if it is possible in Lambdapi to encode a list of Proof.

symbol a: Prop;
symbol b: Prop;
symbol c: Prop;
symbol d: Prop;

symbol eqab ≔ (= a b);
symbol eqbc ≔ = b c;
symbol eqcd ≔ = c d;

// alf.requires is an operator that evalutes to its third argument
// if and only if its first two arguments are equivalent. 
symbol alf-requires [a]:  τ a → τ a → τ a → τ a;
rule alf-requires $x $x $t ↪ $t;

assert a a ⊢ alf-requires a a ⊤ ≡ ⊤;
assert a b ⊢ alf-requires a b ⊤ ≡ alf-requires a b ⊤;

// The ALF language supports a command for defining ordered lists of rewrite rules
// that can be seen as computational side conditions. The syntax for this command is as follows.
// (declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
// (program contains
//     ((l Bool) (x Bool :list) (xs Bool :list))
//     (Bool Bool) Bool
//     (
//         ((contains false l)     false)
//         ((contains (or l xs) l) true)
//         ((contains (or x xs) l) (contains l xs))
//     )
// )
sequential symbol contains: Prop → Prop → Prop;
rule contains ⊥ _ ↪ ⊥
with contains (or $l $x) $l ↪ ⊤
with contains (or $x $xs) $l ↪ contains $l $xs;

// (program mk_trans ((t1 Int) (t2 Int) (t3 Int) (t4 Int) (tail Bool :list))
//     (Int Int Bool) Bool
//     (
//         ((mk_trans t1 t2 (and (= t3 t4) tail)) (alf.requires t2 t3 (mk_trans t1 t4 tail)))
//         ((mk_trans t1 t2 true)                 (= t1 t2))
//     )
// )
sequential symbol mk_trans [a] : τ a → τ a → Prop → Prop;
rule @mk_trans o $t1 $t2 ((@= o $t3 $t4) ∧ $tl) ↪ alf-requires $t2 $t3 (mk_trans $t1 $t4 $tl)
with @mk_trans o $t1 $t2 ⊤ ↪ = $t1 $t2;

// (declare-rule trans (E Bool))
//     :premise-list E and
//     :conclusion
//         (alf.match ((t1 Int) (t2 Int) (tail Bool :list)) E
//         (
//             ((and (= t1 t2) tail) (mk_trans t1 t2 tail))
//         ))
// )
symbol trans: Prop → Prop;
rule trans ((= $t1 $t2) ∧ $tl) ↪ mk_trans $t1 $t2 $tl;

compute trans (premise-list ((= a b) ⸬ (= b c) ⸬ (= c d) ⸬ □) (∧));

assert ⊢ trans (premise-list ((= a b) ⸬ (= b c) ⸬ (= c d) ⸬ □) (∧)) ≡ = a d;


// # We want to translate:
// ; RESOLUTION
// (program resolve ((C1 Bool) (C2 Bool) (pol Bool) (L Bool))
//     (Bool Bool Bool Bool) Bool
//     (
//       ((resolve C1 C2 pol L)
//         (let ((lp (alf.ite pol L (not L))))
//         (let ((ln (alf.ite pol (not L) L)))
//             (alf.from_list or (alf.concat or
//                     (removeSelf lp (list.intro or false C1))
//                     (removeSelf ln (list.intro or false C2)))))))
//     )
// )

// (alf.ite t1 t2 t3) Returns t2 if t1 evaluates to true, t3 if t2 evaluates to false,
// and is not evaluated otherwise. Note that the branches of this term are only evaluated if they are the return term.
sequential symbol ite: Prop → Prop → Prop → Prop;
rule ite ⊤ $t2 _ ↪ $t2
with ite ⊥ _ $t3 ↪ $t3;

// (alf.concat f t1 t2)
// If t1 is an f-list with children t11 ... t1n and t2 is an f-list with children t21 ... t2m,
// this returns (f t11 ... t1n t21 ... t2m) if n+m>0 and nil otherwise. Otherwise, this operator does not evaluate.

/*
(declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
(declare-const and (-> Bool Bool Bool) :right-assoc-nil true)

Below, we assume that `f` is right associative operator with nil terminator `nil` and `t1, t2` are ground. Otherwise, the following operators do not evaluate.
We describe the evaluation for right associative operators; left associative evaluation is defined analogously.
We say that a term is an `f`-list with children `t1 ... tn` if it is of the form `(f t1 ... tn)` where `n>0` or `nil` if `n=0`.


- `(alf.cons f t1 t2)`
- If `t2` is an `f`-list, then this returns the term `(f t1 t2)`.

(alf.cons or a (or a b))            == (or a a b)
(alf.cons or false (or a b))        == (or false a b)
(alf.cons or (or a b) (or b))       == (or (or a b) b)
(alf.cons or false false)           == false
(alf.cons or a b)                   == (alf.cons or a b)                ; since b is not an or-list
(alf.cons or a (or b))              == (or a b)
(alf.cons and (or a b) (and b))     == (and (or a b) b)
(alf.cons and true (and a))         == (and a)
(alf.cons and (and a) true)         == (and (and a))
*/
sequential symbol alf-cons [a]: (τ a → τ a → τ a) → τ a → τ a → τ a;
rule alf-cons (or) $t1 $t2 ↪ or $t1 $t2
with alf-cons (or) ⊥ ⊥ ↪ ⊥;

// (alf.cons or a (or a b))  == (or a a b)
assert ⊢ alf-cons (or) a (or a b) ≡ or a (or a b);
// (alf.cons or false (or a b)) == (or false a b)
assert ⊢ alf-cons (or) ⊥ (or a b) ≡ or ⊥ (or a b);
// (alf.cons or false false) == false
assert ⊢ alf-cons (or) ⊥ ⊥ ≡ ⊥; // or ⊥

//type alf-cons;

// (program list.intro
//     ((L Type) (cons (-> L L L)) (nil L) (intro-nil L) (x L) (xs L :list))
//     ((-> L L L) L L) L
//     (
//         ((list.intro cons nil (cons x xs)) (cons x xs))
//         ((list.intro cons nil nil)         nil)
//         ((list.intro cons nil x)           (alf.cons cons x nil))
//     )
// )
sequential symbol list-intro [L]: (τ L → τ L → τ L) → τ L  → τ L  → τ L;
rule list-intro ($op) $nil $op ↪ $op
with list-intro ($op) $nil $nil ↪ $nil
with list-intro $op $nil $x ↪ alf-cons $op $x $nil;

compute list-intro (or) ⊥ (or a b); 

// ; remove cons c xs
// ; Removes the first occurrence of `c` from `xs`.
// (program nary.remove
//     ((L Type) (cons (-> L L L)) (nil L) (c L) (y L) (xs L :list))
//     ((-> L L L) L L L) L
//     (
//         ((nary.remove cons nil c (cons c xs)) xs)
//         ((nary.remove cons nil c (cons y xs)) (alf.cons cons y (nary.remove cons nil c xs)))
//         ((nary.remove cons nil c nil)         nil)
//     )
// )
sequential symbol nary-remove [L]: (τ L → τ L → τ L) → τ L  →  τ L  → τ L  → τ L;
rule nary-remove (or) $nil $x $nil ↪ $nil
with nary-remove (or) $nil $c (or $y $xs) ↪ alf-cons (or) $y (nary-remove (or) $nil $c $xs)
with nary-remove (or) $nil $c (or $c $xs) ↪ $xs;

symbol p: Prop;
symbol e: Prop;
symbol f: Prop;

compute (nary-remove (or) ⊥ p (or a (or p (or b ⊥))));

sequential symbol alf-is_eq: Prop → Prop → Prop;
rule alf-is_eq $x $y ↪ ⊥
with alf-is_eq $x $x ↪ ⊤;

assert ⊢ alf-is_eq a a ≡ ⊤;
assert ⊢ alf-is_eq a b ≡ ⊥;

// (define removeSelf ((l Bool) (C Bool))
//     (alf.ite (alf.is_eq l C) false (nary.remove or false l C)))
symbol removeSelf (l C: Prop) ≔ ite (alf-is_eq l C) ⊥ (nary-remove (or) ⊥ l C);

// (alf.concat f t1 t2)
// If `t1` is an `f`-list with children `t11 ... t1n` and `t2` is an `f`-list with children `t21 ... t2m`,
// this returns `(f t11 ... t1n t21 ... t2m)` if `n+m>0` and `nil` otherwise.
// Otherwise, this operator does not evaluate.
symbol alf-concat: ( Prop →  Prop →  Prop) → Prop →  Prop →  Prop;
rule alf-concat (or) (or $t1 $t2) (or $t3 $t4) ↪ or $t1 (or $t2 (or $t3 $t4))
with alf-concat (∧) ($t1 ∧ $t2) ($t3 ∧ $t4) ↪ $t1 ∧ ($t2 ∧ ($t3 ∧ $t4));

compute alf-concat (or) (or a (or b c)) (or d (or e f));

sequential symbol alf-from_list: Prop → Prop;
rule alf-from_list (or $x $xs) ↪ or $x (alf-from_list $xs)
with alf-from_list (or $x ⊥) ↪ $x;

assert ⊢ alf-from_list (or a (or b (or c ⊥))) ≡ (or a (or b c));

// ; RESOLUTION
// (program resolve ((C1 Bool) (C2 Bool) (pol Bool) (L Bool))
//     (Bool Bool Bool Bool) Bool
//     (
//       ((resolve C1 C2 pol L)
//         (let ((lp (alf.ite pol L (not L))))
//         (let ((ln (alf.ite pol (not L) L)))
//             (alf.from_list or (alf.concat or
//                     (removeSelf lp (list.intro or false C1))
//                     (removeSelf ln (list.intro or false C2)))))))
//     )
// )

symbol resolve: Prop →  Prop →  Prop →  Prop →  Prop;
rule resolve $C1 $C2 $pol $L ↪
alf-from_list (alf-concat (or)
    (removeSelf  (ite $pol $L (¬ $L)) (list-intro (or) ⊥ $C1))
    (removeSelf  (ite $pol (¬ $L) $L) (list-intro (or) ⊥ $C2)));

compute (resolve (or a p) (or b (¬ p)) ⊤ p); 

// (declare-rule resolution ((C1 Bool) (C2 Bool) (pol Bool) (L Bool))
//     :premises (C1 C2)
//     :args (pol L)
//     :conclusion (resolve C1 C2 pol L)
// )
symbol resolution [a b] (pol L: Prop) : π a → π b → Prop ≔ λ c1, λ c2, resolve a b pol L;

symbol C1: π (or a p);
symbol C2: π (or b (¬ p));
compute (resolution ⊤ p C1 C2); 

// ; CHAIN_RESOLUTION
// ; Applies multiple steps of resolution but leaves the first argument in n-ary form.
// (program chainResolveRec ((C1 Bool) (C2 Bool) (Cs Bool :list) (pol Bool) (L Bool) (args Bool :list))
//     (Bool Bool Bool) Bool
//     (
//         ((chainResolveRec C1 true true)              (alf.from_list or C1))
//         ((chainResolveRec C1 (and C2 Cs) (and pol L args))
//             (chainResolveRec
//                 (let ((lp (alf.ite pol L (not L))))
//                 (let ((ln (alf.ite pol (not L) L)))
//                     (alf.concat or
//                             (removeSelf lp C1)
//                             (removeSelf ln (alf.to_list or C2))))) Cs args))
//     )
// )
sequential symbol chainResolveRec: Prop → Prop → Prop → Prop;
rule chainResolveRec $C1 ⊤ ⊤ ↪ $C1
// with chainResolveRec $C1 ($C2 ∧ $CS) ($pol ∧ ($L ∧ $args)) ↪
//     (chainResolveRec
    
//     $CS $args);
;

// ; This is a chain or resolution steps as described in the cvc5 proof rule
// ; documentation.
// ; `Cs` is a conjunction or the premise clauses.
// ; `args` is a conjunction where the alternating conjuncts are polarity and
// ;        pivot literal.
// (declare-rule chain_resolution ((Cs Bool) (args Bool))
//     :premise-list Cs and
//     :args (args)
//     :conclusion
//         (alf.match ((C1 Bool) (C2 Bool :list))
//             Cs
//             (((and C1 C2) (chainResolveRec (alf.to_list or C1) C2 args))))
//
