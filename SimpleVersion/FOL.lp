require open lisa2dedukti.SimpleVersion.prelude;


constant symbol Formula : TYPE;
constant symbol formula : Set;
rule τ formula ↪ Formula;

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
symbol ⊧ : List formula → List formula → Sequent;
notation ⊧ infix 50;

symbol prf : Sequent → TYPE;
