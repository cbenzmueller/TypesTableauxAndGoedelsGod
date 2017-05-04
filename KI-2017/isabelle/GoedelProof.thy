(*<*)
theory GoedelProof
imports IHOML
begin
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 3,  atoms e = a b c d]
sledgehammer_params[verbose=true]
(*>*)  

section \<open>G\"odel's Ontological Argument\<close>

subsection \<open>Part I - God's Existence is Possible\<close>
(**G\"odel's particular version of the argument is a direct descendent of that of Leibniz, which in turn derives
  from one of Descartes. While Leibniz provides some kind of proof for the compatibility of all perfections,
 G\"odel goes on to prove an analogous result: \emph{(T1) `Every positive property is possibly instantiated'},
 which together with \emph{(T2) `God is a positive property'} directly implies the conclusion.
 In order to prove \emph{T1}, G\"odel assumes \emph{(A2) `Any property entailed by a positive property is itself positive'}.
 As we will see, the success of this argumentation depends on how we choose to formalize our notion of entailment:*)
  
abbreviation Entailment::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>,\<up>\<langle>\<zero>\<rangle>\<rangle>" (infix "\<Rrightarrow>" 60) where
  "X \<Rrightarrow> Y \<equiv>  \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. X z \<^bold>\<rightarrow> Y z)"
lemma "\<lfloor>(\<lambda>x w. x \<noteq> x) \<Rrightarrow> \<chi>\<rfloor>" by simp (**an impossible property entails anything*)
lemma "\<lfloor>\<^bold>\<not>(\<phi> \<Rrightarrow> \<chi>) \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E \<phi>\<rfloor>" by auto (**possible instantiation of @{text "\<phi>"} implicit*)

(**The definition of property entailment introduced by G\"odel can be criticized on the grounds that it lacks
 some notion of relevance and is therefore exposed to the paradoxes of material implication.
 In particular, when we assert that property A does not entail property B, we implicitly assume that
 A is possibly instantiated. Conversely, an impossible property (like being a round square) entails any property
 (like being a triangle). It is precisely by virtue of these paradoxes that G\"odel manages to prove \emph{T1}.
 \footnote{When proving T1 we need to use the fact that positive properties cannot \emph{entail} negative ones (A2), 
 from which the possible instantiation of positive properties follow. 
 A computer-friendly formalization of Leibniz's Theory of Concepts can be found in the work of @{cite "Zalta_Leibniz"}
 where the notion of \emph{concept containment} in contrast to ordinary \emph{property entailment} is discussed at some length.}*)

consts Positiveness::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>" ("\<P>") (**positiveness applies to intensional predicates*)
abbreviation Existence::"\<up>\<langle>\<zero>\<rangle>" ("E!") (**object-language existence predicate*) 
  where "E! x  \<equiv> \<lambda>w. (\<^bold>\<exists>\<^sup>Ey. y\<^bold>\<approx>x) w" 
abbreviation appliesToPositiveProps::"\<up>\<langle>\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>\<rangle>" ("pos") where
  "pos Z \<equiv>  \<^bold>\<forall>X. Z X \<^bold>\<rightarrow> \<P> X"  
abbreviation intersectionOf::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>,\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>\<rangle>" ("intersec") where
  "intersec X Z \<equiv>  \<^bold>\<box>(\<^bold>\<forall>x.(X x \<^bold>\<leftrightarrow> (\<^bold>\<forall>Y. (Z Y) \<^bold>\<rightarrow> (Y x))))"  
  
axiomatization where
  A1a:"\<lfloor>\<^bold>\<forall>X. \<P> (\<^bold>\<rightharpoondown>X) \<^bold>\<rightarrow> \<^bold>\<not>(\<P> X) \<rfloor>" and      (** axiom 11.3A *)
  A1b:"\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<P> (\<^bold>\<rightharpoondown>X)\<rfloor>" and       (** axiom 11.3B *)
  A2: "\<lfloor>\<^bold>\<forall>X Y. (\<P> X \<^bold>\<and> (X \<Rrightarrow> Y)) \<^bold>\<rightarrow> \<P> Y\<rfloor>" and   (** axiom 11.5 *)
  A3: "\<lfloor>\<^bold>\<forall>Z X. (pos Z \<^bold>\<and> intersec X Z) \<^bold>\<rightarrow> \<P> X\<rfloor>" (** axiom 11.10 *)

lemma True nitpick[satisfy] oops    (** model found: axioms are consistent*)
lemma "\<lfloor>D\<rfloor>"  using A1a A1b A2 by blast (**\emph{D} axiom is implicitely assumed*)
    
(** Positive properties are possibly instantiated.*)
theorem T1: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X\<rfloor>" using A1a A2 by blast

(**Being Godlike is defined as having all (and only) positive properties.*)
abbreviation God::"\<up>\<langle>\<zero>\<rangle>" ("G") where "G \<equiv> (\<lambda>x. \<^bold>\<forall>Y. \<P> Y \<^bold>\<rightarrow> Y x)"
abbreviation God_star::"\<up>\<langle>\<zero>\<rangle>" ("G*") where "G* \<equiv> (\<lambda>x. \<^bold>\<forall>Y. \<P> Y \<^bold>\<leftrightarrow> Y x)"
(**Both are equivalent. We can use either one or the other in our proofs.*)
lemma GodDefsAreEquivalent: "\<lfloor>\<^bold>\<forall>x. G x \<^bold>\<leftrightarrow> G* x\<rfloor>" using A1b by force 

(** Being Godlike is itself a positive property.\footnote{This theorem can also be axiomatized directly,
as noted by Dana Scott (see @{cite "Fitting"}, p. 152). We provide here a proof in Isabelle/Isar, a language
specifically tailored for writing proofs that are both computer- and human-readable. Because of space
constraints we can't show the other proofs in this article.}*)
theorem T2: "\<lfloor>\<P> G\<rfloor>" proof -
{ fix w
  have 1: "pos \<P> w" by simp
  have 2: "intersec G \<P> w" by simp
  have "\<lfloor>\<^bold>\<forall>Z X. (pos Z \<^bold>\<and> intersec X Z) \<^bold>\<rightarrow> \<P> X\<rfloor>" by (rule A3)
  hence "(\<^bold>\<forall>Z X. (pos Z \<^bold>\<and> intersec X Z) \<^bold>\<rightarrow> \<P> X) w" by (rule allE)
  hence "(\<^bold>\<forall>X. ((pos \<P>) \<^bold>\<and> (intersec X \<P>)) \<^bold>\<rightarrow> \<P> X) w"  by (rule allE)   
  hence "(((pos \<P>) \<^bold>\<and> (intersec G \<P>)) \<^bold>\<rightarrow> \<P> G) w" by (rule allE)
  hence 3: "((pos \<P> \<^bold>\<and> intersec G \<P>) w) \<longrightarrow> \<P> G w" by simp
  hence 4: "((pos \<P>) \<^bold>\<and> (intersec G \<P>)) w" using 1 2 by simp
  from 3 4 have "\<P> G w" by (rule mp)
} thus ?thesis by (rule allI)
qed    
  
(** Conclusion for the first part: Possibly God exists.*)
theorem T3: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists>\<^sup>E G\<rfloor>"  using T1 T2 by simp
    
subsection \<open>Part II - God's Existence is Necessary, if Possible\<close>
(**In this part we show that God's necessary existence follows from its possible existence by adding some
 additional (philosophically controversial) assumptions including an \emph{essentialist} premise 
 and the \emph{S5} axioms. Further derived results like monotheism and absence of free will are also discussed.*)
        
axiomatization where A4a: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<box>(\<P> X)\<rfloor>"
(** Following lemma was originally assumed by G\"odel as an axiom:*)  
lemma A4b: "\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<not>(\<P> X)\<rfloor>" using A1a A1b A4a by blast
lemma True nitpick[satisfy] oops (**model found: all axioms A1-4 consistent*)

(** Axiom \emph{A4a} and its consequence \emph{A4b} together imply that @{text "\<P>"} satisfies Fitting's
`stability conditions' (@{cite "Fitting"}, p. 124). This means @{text "\<P>"} designates rigidly.
Note that this makes for an \emph{essentialist} assumption which may be considered controversial by
some philosophers: every property considered positive in our world (e.g. honesty) is necessarily so.*)    
lemma "\<lfloor>rigidPred \<P>\<rfloor>" using A4a A4b by blast
    
(**G\"odel defines a particular notion of essence. \emph{Y} is an essence of \emph{x} iff \emph{Y}
\emph{entails} every other property \emph{x} posseses.
\footnote{Essence is defined here (and in Fitting's variant) in the version of Scott; G\"odel's original version
 leads to the inconsistency reported in @{cite "C55,C60"}}*)
abbreviation essenceOf::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>,\<zero>\<rangle>" ("\<E>") where
  "\<E> Y x \<equiv> (Y x) \<^bold>\<and> (\<^bold>\<forall>Z. Z x \<^bold>\<rightarrow> Y \<Rrightarrow> Z)"   
abbreviation beingIdenticalTo::"\<zero>\<Rightarrow>\<up>\<langle>\<zero>\<rangle>" ("id") where
  "id x  \<equiv> (\<lambda>y. y\<^bold>\<approx>x)" (**\emph{id} is here a rigid predicate (following Kripke @{cite "kripke1980"})*)  

(** Being God-like is an essential property:*)  
theorem GodIsEssential: "\<lfloor>\<^bold>\<forall>x. G x \<^bold>\<rightarrow> (\<E> G x)\<rfloor>" using A1b A4a by metis            
(** Something can only have \emph{one} essence:*)
theorem "\<lfloor>\<^bold>\<forall>X Y z. (\<E> X z \<^bold>\<and> \<E> Y z) \<^bold>\<rightarrow> (X \<Rrightarrow> Y)\<rfloor>" by meson  
  
(** An essential property offers a complete characterization of an individual:*)
theorem EssencesCharacterizeCompletely: "\<lfloor>\<^bold>\<forall>X y. \<E> X y \<^bold>\<rightarrow> (X \<Rrightarrow> (id y))\<rfloor>"
  proof (rule ccontr) (**Isar proof by contradiction not shown here*)
(*<*) assume "\<not> \<lfloor>\<^bold>\<forall>X y. \<E> X y \<^bold>\<rightarrow> (X \<Rrightarrow> (id y))\<rfloor>"
  hence "\<exists>w. \<not>(( \<^bold>\<forall>X y. \<E> X y \<^bold>\<rightarrow> X \<Rrightarrow> id y) w)" by simp
  then obtain w where "\<not>(( \<^bold>\<forall>X y. \<E> X y \<^bold>\<rightarrow> X \<Rrightarrow> id y) w)" ..
  hence "(\<^bold>\<exists>X y. \<E> X y \<^bold>\<and> \<^bold>\<not>(X \<Rrightarrow> id y)) w" by simp
  hence "\<exists>X y. \<E> X y w \<and> (\<^bold>\<not>(X \<Rrightarrow> id y)) w" by simp
  then obtain P where "\<exists>y. \<E> P y w \<and> (\<^bold>\<not>(P \<Rrightarrow> id y)) w" ..
  then obtain a where 1: "\<E> P a w \<and> (\<^bold>\<not>(P \<Rrightarrow> id a)) w" ..
  hence 2: "\<E> P a w" by (rule conjunct1)
  from 1 have "(\<^bold>\<not>(P \<Rrightarrow> id a)) w" by (rule conjunct2)
  hence "\<exists>x. \<exists>z. w r x \<and>  z existsAt x \<and> P z x \<and> \<not>(a = z)" by blast
  then obtain w1 where "\<exists>z. w r w1 \<and>  z existsAt w1 \<and> P z w1 \<and> \<not>(a = z)" ..
  then obtain b where 3: "w r w1 \<and>  b existsAt w1 \<and> P b w1 \<and> \<not>(a = b)" ..
  hence "w r w1" by simp
  from 3 have "b existsAt w1" by simp
  from 3 have "P b w1" by simp
  from 3 have 4: " \<not>(a = b)" by simp
  from 2 have "P a w" by simp
  from 2 have "\<forall>Y. Y a w \<longrightarrow> ((P \<Rrightarrow> Y) w)" by auto
  hence "(\<^bold>\<rightharpoondown>(id b)) a w \<longrightarrow> (P \<Rrightarrow> (\<^bold>\<rightharpoondown>(id b))) w" by (rule allE)
  hence "\<not>(\<^bold>\<rightharpoondown>(id b)) a w \<or> ((P \<Rrightarrow> (\<^bold>\<rightharpoondown>(id b))) w)" by blast 
  then show False proof
    assume "\<not>(\<^bold>\<rightharpoondown>(id b)) a w"
    hence "a = b" by simp
    thus False using 4 by auto
    next  
    assume "((P \<Rrightarrow> (\<^bold>\<rightharpoondown>(id b))) w)"
    hence "\<forall>x. \<forall>z. (w r x \<and> z existsAt x \<and> P z x) \<longrightarrow> (\<^bold>\<rightharpoondown>(id b)) z x" by blast
    hence "\<forall>z. (w r w1 \<and> z existsAt w1 \<and> P z w1) \<longrightarrow> (\<^bold>\<rightharpoondown>(id b)) z w1" 
        by (rule allE)
    hence "(w r w1 \<and> b existsAt w1 \<and> P b w1) \<longrightarrow> (\<^bold>\<rightharpoondown>(id b)) b w1" by (rule allE)
    hence  "\<not>(w r w1 \<and> b existsAt w1 \<and> P b w1) \<or> (\<^bold>\<rightharpoondown>(id b)) b w1" by simp
    hence "(\<^bold>\<rightharpoondown>(id b)) b w" using 3 by simp
    hence "\<not>(b=b)" by simp
    thus False by simp
  qed
qed
  (*>*)
(**G\"odel introduces a particular notion of \emph{necessary existence} as the property something has
 provided any essence of it is necessarily instantiated:*)
abbreviation necessaryExistencePredicate::"\<up>\<langle>\<zero>\<rangle>" ("NE") 
  where "NE x  \<equiv> (\<lambda>w. (\<^bold>\<forall>Y.  \<E> Y x \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E Y) w)"

axiomatization where A5: "\<lfloor>\<P> NE\<rfloor>" (**necessary existence is a positive property*)
lemma True nitpick[satisfy] oops (**model found: so far all axioms consistent*)
 
(**(Possibilist) existence of God implies its necessary (actualist) existence:*)
theorem GodExistenceImpliesNecEx: "\<lfloor>\<^bold>\<exists> G \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<rfloor>" proof - (**not shown*)
(*<*)
{
  fix w 
  {
    assume "\<exists>x. G x w"
    then obtain g where 1: "G g w" ..
    hence "NE g w" using A5 by auto                     (** axiom 11.25*)
    hence "\<forall>Y. (\<E> Y g w) \<longrightarrow> (\<^bold>\<box>\<^bold>\<exists>\<^sup>E Y) w" by simp
    hence 2: "(\<E> G g w) \<longrightarrow> (\<^bold>\<box>\<^bold>\<exists>\<^sup>E G) w" by (rule allE)
    have  "(\<^bold>\<forall>x. G x \<^bold>\<rightarrow> (\<E> G x)) w" using GodIsEssential
      by (rule allE)     (** GodIsEssential follows from Axioms 11.11 and 11.3B *)
    hence  "(G g \<^bold>\<rightarrow> (\<E> G g)) w" by (rule allE)
    hence  "G g w \<longrightarrow> \<E> G g w" by simp
    from this 1 have 3: "\<E> G g w" by (rule mp)
    from 2 3 have "(\<^bold>\<box>\<^bold>\<exists>\<^sup>E G) w" by (rule mp)
  }
  hence "(\<exists>x. G x w) \<longrightarrow> (\<^bold>\<box>\<^bold>\<exists>\<^sup>E G) w" by (rule impI)
  hence "((\<^bold>\<exists>x. G x) \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<exists>\<^sup>E G) w" by simp
}
  thus ?thesis by (rule allI) 
qed
(*>*)
(** Below we postulate semantic frame conditions for some modal logics. \footnote{Taken together, reflexivity, transitivity and symmetry
 make for an equivalence relation and therefore an \emph{S5} logic (via \emph{Sahlqvist correspondence}).
 They are individually postulated in order to get more detailed information about their relevance in the proofs presented below.}*)
axiomatization where
 refl: "reflexive aRel" and tran: "transitive aRel" and symm: "symmetric aRel"
 
lemma True nitpick[satisfy] oops (** model found: axioms still consistent*)
(*<*)   
(** We prove some useful inference rules:*)    
lemma modal_distr: "\<lfloor>\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<psi>)\<rfloor> \<Longrightarrow> \<lfloor>(\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<psi>)\<rfloor>" by blast
lemma modal_trans: "(\<lfloor>\<phi> \<^bold>\<rightarrow> \<psi>\<rfloor> \<and> \<lfloor>\<psi> \<^bold>\<rightarrow> \<chi>\<rfloor>) \<Longrightarrow> \<lfloor>\<phi> \<^bold>\<rightarrow> \<chi>\<rfloor>" by simp
(*>*)
(**Possible existence of God implies its necessary (actualist) existence (note that only symmetry and
transitivity are needed as frame conditions):*)
theorem T4: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> G\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<rfloor>" proof - (** not shown*)
(*<*)
  have "\<lfloor>\<^bold>\<exists> G \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<rfloor>" using GodExistenceImpliesNecEx by simp (* follows from Axioms 11.11, 11.25 and 11.3B*)
  hence "\<lfloor>\<^bold>\<box>(\<^bold>\<exists> G \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G)\<rfloor>" using NEC by simp
  hence 1: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> G \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<rfloor>" by (rule modal_distr)
  have 2: "\<lfloor>\<^bold>\<diamond>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<rfloor>" using symm tran by metis (**frame conditions*)
  from 1 2 have "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> G \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<rfloor> \<and> \<lfloor>\<^bold>\<diamond>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<rfloor>" by simp
  hence "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> G \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<rfloor>" by (rule modal_trans)
  thus ?thesis by (rule localImpGlobalCons)
qed
(*>*)  
(** Conclusion: Necessary (actualist) existence of God: *)    
theorem GodNecExists: "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<rfloor>" using T3 T4 by metis
(** To prove validity we still need reflexivity for our frame conditions:*)    
theorem GodExistenceIsValid: "\<lfloor>\<^bold>\<exists>\<^sup>E G\<rfloor>" using GodNecExists refl by auto
    
(**Monotheism for non-normal models (using Leibniz equality) follows directly from God having all
and only positive properties, but the proof for normal models is trickier. We need to consider previous results
 (@{cite "Fitting"}, p. 162):*)
theorem Monotheism_LeibnizEq:"\<lfloor>\<^bold>\<forall>x. G* x \<^bold>\<rightarrow> (\<^bold>\<forall>y. G* y \<^bold>\<rightarrow> x\<^bold>\<approx>\<^sup>Ly)\<rfloor>" by meson
theorem Monotheism_normal: "\<lfloor>\<^bold>\<exists>x.\<^bold>\<forall>y. G y \<^bold>\<leftrightarrow> x \<^bold>\<approx> y\<rfloor>" proof - (**not shown*)
(*<*)
{
  fix w 
  have "\<lfloor>\<^bold>\<exists>\<^sup>E G\<rfloor>" using GodExistenceIsValid by simp (* follows from corollary 11.28*)
  hence "(\<^bold>\<exists>\<^sup>E G) w" by (rule allE)       
  then obtain g where 1: "g existsAt w \<and> G g w" ..
  hence 2: "\<E> G g w" using GodIsEssential by blast (*follows from ax. 11.11/11.3B*)
  {
    fix y
    have "G y w \<longleftrightarrow> (g \<^bold>\<approx> y) w" proof 
      assume "G y w"
      hence 3: "\<E> G y w" using GodIsEssential by blast      
      have "(\<E> G y \<^bold>\<rightarrow> (G \<Rrightarrow> id y)) w" using EssencesCharacterizeCompletely
        by simp (** follows from theorem 11.23 *)
      hence "\<E> G y w \<longrightarrow> ((G \<Rrightarrow> id y) w)" by simp
      from this 3 have "(G \<Rrightarrow> id y) w" by (rule mp) 
      hence "(\<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. G z \<^bold>\<rightarrow> z \<^bold>\<approx> y)) w" by simp
      hence "\<forall>x. w r x \<longrightarrow> ((\<forall>z. (z existsAt x \<and> G z x) \<longrightarrow> z = y))" by auto
      hence "w r w \<longrightarrow> ((\<forall>z. (z existsAt w \<and> G z w) \<longrightarrow> z = y))" by (rule allE)
      hence "\<forall>z. (w r w \<and> z existsAt w \<and> G z w) \<longrightarrow> z = y" by auto
      hence 4: "(w r w \<and> g existsAt w \<and> G g w) \<longrightarrow> g = y" by (rule allE)
      have "w r w" using refl 
        by simp (** using frame reflexivity (Axiom M)*)
      hence  "w r w \<and> (g existsAt w \<and> G g w)" using 1 by (rule conjI)
      from 4 this have "g = y" by (rule mp)
      thus "(g \<^bold>\<approx> y) w" by simp
    next
      assume "(g \<^bold>\<approx> y) w"
      from this 2 have "\<E> G y w" by simp
      thus "G y w " by (rule conjunct1)
    qed
  }
  hence "\<forall>y. G y w \<longleftrightarrow> (g \<^bold>\<approx> y) w" by (rule allI) 
  hence "\<exists>x. (\<forall>y. G y w \<longleftrightarrow> (x \<^bold>\<approx> y) w)" by (rule exI) 
  hence "(\<^bold>\<exists>x. (\<^bold>\<forall>y. G y \<^bold>\<leftrightarrow> (x \<^bold>\<approx> y))) w" by simp
}
  thus ?thesis by (rule allI) 
qed
  
lemma useful: "(\<forall>x. \<phi> x \<longrightarrow> \<psi>) \<Longrightarrow> ((\<exists>x. \<phi> x) \<longrightarrow> \<psi>)" by simp
(*>*)
(**Fitting @{cite "Fitting"} also discusses the objection raised by Sobel @{cite "sobel2004logic"}, who argues that G\"odel's axiom system
is too strong: it implies that whatever is the case is so necessarily, i.e. the modal system collapses (@{text "\<phi> \<longrightarrow> \<box>\<phi>"}).
This has been philosophically interpreted as implying the absence of free will.    
In the context of our S5 axioms, the \emph{modal collapse} becomes valid (@{cite "Fitting"}, pp. 163-4): *)     
theorem ModalCollapse: "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>" proof - (**not shown here*)
(*<*)
  { fix w
   { fix Q
    have "(\<^bold>\<forall>x. G x \<^bold>\<rightarrow> (\<E> G x)) w" using GodIsEssential by (rule allE) (* follows from Axioms 11.11 and 11.3B *)
    hence "\<forall>x. G x w \<longrightarrow> \<E> G x w" by simp
    hence "\<forall>x. G x w \<longrightarrow> (\<^bold>\<forall>Z. Z x \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. G z \<^bold>\<rightarrow> Z z)) w" by force
    hence "\<forall>x. G x w \<longrightarrow> ((\<lambda>y. Q) x \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. G z \<^bold>\<rightarrow> (\<lambda>y. Q) z)) w" by force
    hence "\<forall>x. G x w \<longrightarrow> (Q \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. G z \<^bold>\<rightarrow> Q)) w" by simp
    hence 1: "(\<exists>x. G x w) \<longrightarrow> ((Q \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. G z \<^bold>\<rightarrow> Q)) w)" by (rule useful)
    have "\<exists>x. G x w" using GodExistenceIsValid by auto
    from 1 this have "(Q \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. G z \<^bold>\<rightarrow> Q)) w" by (rule mp)
    hence "(Q \<^bold>\<rightarrow> \<^bold>\<box>((\<^bold>\<exists>\<^sup>Ez. G z) \<^bold>\<rightarrow> Q)) w" using useful by blast
    hence "(Q \<^bold>\<rightarrow> (\<^bold>\<box>(\<^bold>\<exists>\<^sup>Ez. G z) \<^bold>\<rightarrow> \<^bold>\<box>Q)) w" by simp
    hence "(Q \<^bold>\<rightarrow> \<^bold>\<box>Q) w" using GodNecExists by simp
   } hence "(\<^bold>\<forall>\<Phi>. \<Phi> \<^bold>\<rightarrow> \<^bold>\<box> \<Phi>) w" by (rule allI)
  } thus ?thesis by (rule allI)
qed
end
(*>*)
