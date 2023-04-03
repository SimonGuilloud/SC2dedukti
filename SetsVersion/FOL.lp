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

symbol mapS : (Formula → Formula) → SetF → SetF;
rule mapS _ EmptyF ↪ EmptyF;
rule mapS $f (SingleF $x) ↪ SingleF ($f $x);
rule mapS $f ($s ∪ $t) ↪ (mapS $f $s) ∪ (mapS $f $t);
rule mapS $f ($x ** $s) ↪ ($f $x) ** (mapS $f $s);





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

//Disjonction
associative commutative symbol ∨ : Formula → Formula → Formula;
notation ∨ infix right 30;
associative commutative symbol ∧ : Formula → Formula → Formula;
notation ∧ infix right 30;

symbol set2and : SetF → Formula;

rule set2and EmptyF ↪ Top;
rule set2and (SingleF $x) ↪ $x;
rule set2and ($x ∪ $y) ↪ (set2and $x) ∧ (set2and $y);


symbol set2or : SetF → Formula;

rule set2or EmptyF ↪ Bot;
rule set2or (SingleF $x) ↪ $x;
rule set2or ($x ∪ $y) ↪ (set2or $x) ∧ (set2or $y);



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


compute ((Top ** Top ** Bot ** (Bot ∧ Top) ** EmptyF) ∪ (Top ** Bot ** Top ** EmptyF));
