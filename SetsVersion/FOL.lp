require open lisa2dedukti.SetsVersion.prelude;
constant symbol Formula : TYPE;
constant symbol formula : Set;
rule τ formula ↪ Formula;

constant symbol Term : TYPE;
constant symbol term : Set;
rule τ term ↪ Term;

constant symbol Id: TYPE;
constant symbol 0:Id;



// Sets


constant symbol SetF: TYPE;
constant symbol EmptyF : SetF;
constant symbol SingleF : Formula → SetF;
//associative commutative symbol ** : Formula → SetF → SetF;
associative commutative symbol ∪ : SetF → SetF → SetF;
notation ∪ infix right 20;
symbol ** ϕ s ≔ (SingleF ϕ) ∪ s;
notation ** infix right 19;

rule (SingleF $x) ∪ (SingleF $x) ↪ SingleF $x;
rule (SingleF $x) ∪ ((SingleF $x) ∪ $l) ↪ SingleF $x ∪ $l;
rule $s ∪ EmptyF ↪ $s;
rule EmptyF ∪ $s ↪ $s;



/*
constant symbol S: Id → Id;

symbol x ≔ 0;
symbol y ≔ S 0;
symbol z ≔ S (S 0);

constant symbol V : Id → Formula;
*/

constant symbol Equality : Term → Term → Formula;

constant symbol Top : Formula;
constant symbol Bot : Formula;

symbol Neg : Formula → Formula;
symbol Implies : Formula → Formula → Formula;
symbol Iff : Formula → Formula → Formula;
symbol And : SetF → Formula;
symbol Or  : SetF → Formula;




// symbol form2sequent :
// rule  And Nil ↪ seq Nil;

constant symbol Forall : (Term → Formula) → Formula;
constant symbol Exists : (Term → Formula) → Formula;
symbol ExistsOne : (Term → Formula) → Formula;

constant symbol Sequent : TYPE;
symbol seq : SetF → SetF → Sequent;
//type Implies (V x) (Or (V x) (And (V y) (V z)));

symbol myfirst-sequent ≔ λ x : Formula,  λ y : Formula, seq  (SingleF (Neg x) ) (SingleF y) ;

constant symbol prf : Sequent → TYPE;


compute (Top ** Top ** Bot ** (And (SingleF Bot)) ** Top ** EmptyF) ∪ (Top ** Bot ** Top ** EmptyF);
