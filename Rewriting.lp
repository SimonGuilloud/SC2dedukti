require open lisa2dedukti.FOL;
require open lisa2dedukti.prelude;
require open lisa2dedukti.SequentCalculus;
// ≔ λ x, prf (seq (ϕ x) (ψ x)) → prf (seq (ϕ t) (ψ t)) ;

// Builtin
// Syntactic sugar - And, Iff, Implies, ExistsOne


rule And $l ↪ Neg (Or (map Neg $l));
rule Iff $ϕ $ψ ↪ And ((Implies $ϕ $ψ) ⸬ (Implies $ψ $ϕ) ⸬ Nil);
rule Implies $ϕ $ψ ↪ Or ((Neg $ϕ) ⸬ $ψ ⸬ Nil) ;
rule ExistsOne $f ↪ Forall (λ y, (Exists (λ x, Iff (Equality x y) ($f x))));

// Rewriting rules

rule Or Nil ↪ Top;

// A1 - Commutativité

// A2 - Associativité

symbol norm : Formula → Formula;
symbol flatten : List formula → List formula ;
rule flatten Nil ↪ Nil;
rule flatten ((Or $l1) ⸬ $l2) ↪ append (flatten $l1) (flatten $l2);
rule flatten ((Neg $x) ⸬ $l) ↪ (Neg (norm $x)) ⸬ (flatten $l);
rule flatten (Bot ⸬ $l) ↪ Bot ⸬ (flatten $l);
rule flatten (Top ⸬ $l) ↪ Bot ⸬ (flatten $l);

// rule norm (Or ((Or $l1) ⸬ $l2)) ↪ Or (append (norm $l1) (norm $l2));
// rule Or ((Or $l1) ⸬ $l2) ↪ Or (append $l1 $l2);

rule norm (Or ((Or $l1) ⸬ $l2)) ↪ Or (append (flatten $l1) (flatten $l2)) ;

compute norm (Or (Or (Top ⸬ Nil) ⸬ Bot ⸬ (Or (Bot ⸬ Nil)) ⸬ Nil));

rule Or ($x ⸬ Nil) ↪ $x;

// A3 -
// rule Or

// A4 -
// rule

// A5

rule Neg (Neg $x) ↪ $x;

rule Neg Bot ↪ Top;
rule Neg Top ↪ Bot;

