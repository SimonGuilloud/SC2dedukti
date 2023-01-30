require open lisa2dedukti.SetsVersion.FOL;
require open lisa2dedukti.SetsVersion.prelude;

// Susucre

rule $ϕ ∧ $ψ ↪ Neg ((Neg $ϕ) ∨ (Neg $ψ));
rule Iff $ϕ $ψ ↪ (Implies $ϕ $ψ) ∧ (Implies $ψ $ϕ);
rule Implies $ϕ $ψ ↪ (Neg $ϕ) ∨ $ψ ;
rule ExistsOne $f ↪ Forall (λ y, (Exists (λ x, Iff (Equality x y) ($f x))));


// A1 is offered by AC representation of ∨

// A2 : is offered by AC representation of ∨

// A3 Idempotence

rule $ϕ ∧ $ϕ ↪ $ϕ;

// A4 : Simplification of Top
rule Top ∨ $f ↪ Top;
rule $f ∨ Top ↪ Top;


// A5 : Simplification of Bot
rule Bot ∨ $f ↪ $f;
rule $f ∨ Bot ↪ $f;


// A6 : Double Negation elimination
rule (Neg (Neg $x)) ↪ $x;

// A7 : Contradiction probably not possible without custom order
//rule $x ∨ (Neg $x) ↪ Top;
//rule (Neg $x) ∨ $x ↪ Top;
//no guarantee the order Dedukti will use is the same 

compute λ x, λ y, x ∨ y ∨ (Neg x);
compute λ x, λ y, x ∨ y ∨ (Neg x) ∨ (Neg y);
compute λ x, λ y, x ∨ (Neg x) ∨ y ∨ (Neg y);

//symbol contrad  : Π x, Π s1, Π s2, Π s3, prf (seq EmptyF ((s1 ∨ x ∨ s2 ∨ (Neg x) ∨ s3) ** EmptyF)) → prf (seq EmptyF (SingleF Top)) ;

//A9 : may not be pssible without custom order as



//A10 : 
rule (Neg Top) ↪ Bot;

//A11 :
rule (Neg Bot) ↪ Top;
