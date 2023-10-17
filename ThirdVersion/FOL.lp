
// Interpretation of set codes in TYPE
constant symbol T0 : TYPE;
injective symbol τ : T0 → TYPE;

// Definition of Formulas
constant symbol Formula : TYPE;
constant symbol formula : T0;
rule τ formula ↪ Formula;



// Definition of Sets
constant symbol Set :  TYPE;
constant symbol Nil : Set;
constant symbol Sing : Formula → Set;
commutative associative symbol u : Set → Set → Set;
notation u infix right 20;
rule $x u $x ↪ $x; //idempotence of sets
symbol ⸬  : Formula → Set → Set ≔ λ e s, (Sing e) u s;

notation ⸬ infix right 20;

constant symbol Term : TYPE;


symbol Equality : Term → Term → Formula;

symbol Top : Formula;
symbol Bot : Formula;

symbol ∧ : Formula → Formula → Formula; notation ∧ infix right 30;
symbol ∨ : Formula → Formula → Formula; notation ∨ infix right 30;
symbol Implies : Formula → Formula → Formula;

symbol Forall : (Term → Formula) → Formula;
symbol Exists : (Term → Formula) → Formula;

symbol Neg : Formula → Formula;
symbol Iff : Formula → Formula → Formula;
symbol ExistsOne : (Term → Formula) → Formula;


symbol Sequent : TYPE;
symbol ⊧ : Set → Set → Sequent;
notation ⊧ infix 50;

symbol prf : Sequent → TYPE;
