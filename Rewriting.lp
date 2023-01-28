require open lisa2dedukti.FOL;
require open lisa2dedukti.prelude;



constant symbol RedForm : TYPE;
constant symbol redForm : Set;
rule τ redForm ↪ RedForm;

symbol norm : Formula → RedForm;

constant symbol RedTop : RedForm;
constant symbol RedBot : RedForm;
constant symbol RedOr : (List redForm) → RedForm;
constant symbol RedNeg : RedForm → RedForm;
constant symbol RedForall : (Term → RedForm) → RedForm;
constant symbol RedExists : (Term → RedForm) → RedForm;



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

symbol flatFormula : Formula → RedForm;
symbol flatten : List formula → List redForm ;

rule flatFormula (Or $l) ↪ (RedOr (flatten $l));
rule flatFormula (Neg $x) ↪ (RedNeg (flatFormula $x));
rule flatFormula Top ↪ RedTop;
rule flatFormula Bot ↪ RedBot;

rule flatten Nil ↪ Nil;
rule flatten ((Or $l1) ⸬ $l2) ↪ append (flatten $l1) (flatten $l2);
rule flatten ($x ⸬ $l) ↪ (flatFormula $x) ⸬ (flatten $l);
/*
rule flatten ((Neg $x) ⸬ $l) ↪ (RedNeg (flatFormula $x)) ⸬ (flatten $l);
rule flatten (Bot ⸬ $l) ↪ RedBot ⸬ (flatten $l);
rule flatten (Top ⸬ $l) ↪ RedTop ⸬ (flatten $l);
*/
rule norm $f ↪ flatFormula $f;

compute norm (Or (Or (Top ⸬ (Or ((Neg Top) ⸬ Top ⸬ Nil) ) ⸬ Nil) ⸬ Bot ⸬ (Or (Bot ⸬ (Neg Bot) ⸬ Nil)) ⸬ Nil));

compute  λ (x:Formula), (norm (Or (x ⸬ (Or (Top ⸬ Bot ⸬ Nil)) ⸬ Nil)));
compute  λ (x:Formula), (norm (Or (x ⸬ Top ⸬ Bot ⸬ Nil)));




symbol RemoveDuplicate : RedForm → RedForm;
symbol RemoveX (x:RedForm) (l: List redForm): RedForm;

//rule RemoveX $x ($y ⸬ $l) ↪ 


// A3 -
// rule Or



/*
// A4 -
// rule

// A5

rule Neg (Neg $x) ↪ $x;

rule Neg Bot ↪ Top;
rule Neg Top ↪ Bot;

*/
