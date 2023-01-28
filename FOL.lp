require open lisa2dedukti.prelude;
constant symbol Formula : TYPE;
constant symbol formula : Set;
rule τ formula ↪ Formula;

constant symbol Term : TYPE;
constant symbol term : Set;
rule τ term ↪ Term;

constant symbol Id: TYPE;
constant symbol 0:Id;



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
symbol And : List formula → Formula;
symbol Or  : List formula → Formula;

symbol HOLE : Formula ;

// x ∨ ¬ x
symbol toto ≔ λ x : Formula, Or ( x ⸬ (Neg x)  ⸬ Nil);

compute toto HOLE;


// symbol form2sequent :
// rule  And Nil ↪ seq Nil;

constant symbol Forall : (Term → Formula) → Formula;
constant symbol Exists : (Term → Formula) → Formula;
symbol ExistsOne : (Term → Formula) → Formula;

constant symbol Sequent : TYPE;
constant symbol seq : List formula → List formula → Sequent;
//type Implies (V x) (Or (V x) (And (V y) (V z)));

symbol myfirst-sequent ≔ λ x : Formula,  λ y : Formula, seq  ((Neg x) ⸬ Nil) (y ⸬ Nil) ;

constant symbol prf : Sequent → TYPE;

