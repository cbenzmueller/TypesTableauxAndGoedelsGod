(*<*)
theory GoedelProof_P1
imports IHOML
begin
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 3,  atoms e = a b c d]
sledgehammer_params[verbose=true]
(*>*)  

section \<open>G\"odel's Argument, Formally\<close>

(**
 "G\"odel's particular version of the argument is a direct descendent of that of Leibniz, which in turn derives
  from one of Descartes. These arguments all have a two-part structure: prove God's existence is necessary,
  if possible; and prove God's existence is possible." @{cite "Fitting"}, p. 138.*) 

subsection \<open>Part I - God's Existence is Possible\<close>

(** We separate G\"odel's Argument as presented in Fitting's textbook (ch. 11) in two parts. For the first one, while Leibniz provides
  some kind of proof for the compatibility of all perfections, G\"odel goes on to prove an analogous result:
 \emph{(T1) Every positive property is possibly instantiated}, which together with \emph{(T2) God is a positive property}
  directly implies the conclusion. In order to prove \emph{T1}, G\"odel assumes \emph{A2: Any property entailed by a positive property is positive}.*)
(** We are currently contemplating a follow-up analysis of the philosophical implications of these axioms,
 which encompasses some criticism of the notion of \emph{property entailment} used by G\"odel throughout the argument.*)
  
  (** We show here that God's necessary existence follows from its possible existence by adding some
 additional (potentially controversial) assumptions including an \emph{essentialist} premise 
 and the \emph{S5} axioms.
 Further results like monotheism and the rejection of free will (\emph{modal collapse}) are also proved.
 *)
  
subsubsection \<open>General Definitions\<close>
(** Definitions used throughout the argument.*)
               
abbreviation existencePredicate::"\<up>\<langle>\<zero>\<rangle>" ("E!") 
  where "E! x  \<equiv> \<lambda>w. (\<^bold>\<exists>\<^sup>Ey. y\<^bold>\<approx>x) w" (**existence predicate in object language*)
    
lemma "E! x w \<longleftrightarrow> existsAt x w" 
  by simp (**safety check: @{text "E!"} correctly matches its meta-logical counterpart*)

consts positiveProperty::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>" ("\<P>") (** positiveness/perfection *)
  
(** Definitions of God (later shown to be equivalent under axiom \emph{A1b}): *)    
abbreviation God::"\<up>\<langle>\<zero>\<rangle>" ("G") where "G \<equiv> (\<lambda>x. \<^bold>\<forall>Y. \<P> Y \<^bold>\<rightarrow> Y x)"
abbreviation God_star::"\<up>\<langle>\<zero>\<rangle>" ("G*") where "G* \<equiv> (\<lambda>x. \<^bold>\<forall>Y. \<P> Y \<^bold>\<leftrightarrow> Y x)"
  
(** Definitions needed to formalise \emph{A3}: *)
abbreviation appliesToPositiveProps::"\<up>\<langle>\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>\<rangle>" ("pos") where
  "pos Z \<equiv>  \<^bold>\<forall>X. Z X \<^bold>\<rightarrow> \<P> X"  
abbreviation intersectionOf::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>,\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>\<rangle>" ("intersec") where
  "intersec X Z \<equiv>  \<^bold>\<box>(\<^bold>\<forall>x.(X x \<^bold>\<leftrightarrow> (\<^bold>\<forall>Y. (Z Y) \<^bold>\<rightarrow> (Y x))))" (**quantifier is possibilist*)  
abbreviation Entailment::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>,\<up>\<langle>\<zero>\<rangle>\<rangle>" (infix "\<Rrightarrow>" 60) where
  "X \<Rrightarrow> Y \<equiv>  \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. X z \<^bold>\<rightarrow> Y z)"
  
subsubsection \<open>Axioms\<close>
    
axiomatization where
  A1a:"\<lfloor>\<^bold>\<forall>X. \<P> (\<^bold>\<rightharpoondown>X) \<^bold>\<rightarrow> \<^bold>\<not>(\<P> X) \<rfloor>" and      (** axiom 11.3A *)
  A1b:"\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<P> (\<^bold>\<rightharpoondown>X)\<rfloor>" and       (** axiom 11.3B *)
  A2: "\<lfloor>\<^bold>\<forall>X Y. (\<P> X \<^bold>\<and> (X \<Rrightarrow> Y)) \<^bold>\<rightarrow> \<P> Y\<rfloor>" and   (** axiom 11.5 *)
  A3: "\<lfloor>\<^bold>\<forall>Z X. (pos Z \<^bold>\<and> intersec X Z) \<^bold>\<rightarrow> \<P> X\<rfloor>" (** axiom 11.10 *)

lemma True nitpick[satisfy] oops       (** model found: axioms are consistent*)
    
lemma "\<lfloor>D\<rfloor>"  using A1a A1b A2 by blast (** axioms already imply \emph{D} axiom *)
lemma "\<lfloor>D\<rfloor>" using A1a A3 by metis

subsubsection \<open>Theorems\<close>
    
lemma "\<lfloor>\<^bold>\<exists>X. \<P> X\<rfloor>" using A1b by auto
lemma "\<lfloor>\<^bold>\<exists>X. \<P> X \<^bold>\<and>  \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X\<rfloor>" using A1a A1b A2 by metis
 
(** Proposition 11.8 (Informal Proposition 1) - Positive properties are possibly instantiated: *)
theorem T1: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X\<rfloor>" using A1a A2 by blast
    
(** Proposition 11.14 - Both defs (\emph{God/God*}) are equivalent. For improved performance we may prefer to use one or the other: *)
lemma GodDefsAreEquivalent: "\<lfloor>\<^bold>\<forall>x. G x \<^bold>\<leftrightarrow> G* x\<rfloor>" using A1b by force 

(** Proposition 11.16 - \emph{A3} implies \emph{P(G)} (local consequence):  *)   
lemma A3implT2_local: "\<lfloor>(\<^bold>\<forall>Z X. (pos Z \<^bold>\<and> intersec X Z) \<^bold>\<rightarrow> \<P> X) \<^bold>\<rightarrow> \<P> G\<rfloor>"
proof -
  {
  fix w
  have 1: "pos \<P> w" by simp
  have 2: "intersec G \<P> w" by simp
  {    
    assume "(\<^bold>\<forall>Z X. (pos Z \<^bold>\<and> intersec X Z) \<^bold>\<rightarrow> \<P> X) w"
    hence "(\<^bold>\<forall>X. ((pos \<P>) \<^bold>\<and> (intersec X \<P>)) \<^bold>\<rightarrow> \<P> X) w"  by (rule allE)   
    hence "(((pos \<P>) \<^bold>\<and> (intersec G \<P>)) \<^bold>\<rightarrow> \<P> G) w" by (rule allE)
    hence 3: "((pos \<P> \<^bold>\<and> intersec G \<P>) w) \<longrightarrow> \<P> G w" by simp
    hence 4: "((pos \<P>) \<^bold>\<and> (intersec G \<P>)) w" using 1 2 by simp
    from 3 4 have "\<P> G w" by (rule mp)
  }
  hence "(\<^bold>\<forall>Z X. (pos Z \<^bold>\<and> intersec X Z) \<^bold>\<rightarrow> \<P> X) w  \<longrightarrow> \<P> G w" by (rule impI)
  } 
  thus ?thesis by (rule allI)
qed    
    
(** \emph{A3} implies @{text "P(G)"} (as global consequence):*)
lemma A3implT2_global: "\<lfloor>\<^bold>\<forall>Z X. (pos Z \<^bold>\<and> intersec X Z) \<^bold>\<rightarrow> \<P> X\<rfloor> \<longrightarrow> \<lfloor>\<P> G\<rfloor>" 
  using A3implT2_local by (rule localImpGlobalCons) 
  
(** Being Godlike is a positive property. Note that this theorem can be axiomatized directly,
as noted by Dana Scott (see @{cite "Fitting"}, p. 152).*)
theorem T2: "\<lfloor>\<P> G\<rfloor>" using A3implT2_global A3 by simp
  
(** (Informal Proposition 3) - Possibly God exists:*)
theorem T3: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists>\<^sup>E G\<rfloor>"  using T1 T2 by simp
    
subsubsection \<open>Axioms\<close>
        
(** @{text "\<P>"} satisfies the so-called stability conditions (see @{cite "Fitting"}, p. 124), which means
 it designates rigidly (note that this makes for an \emph{essentialist} assumption).*)
axiomatization where
      A4a: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<box>(\<P> X)\<rfloor>"      (** axiom 11.11 *)
lemma A4b: "\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<not>(\<P> X)\<rfloor>" using A1a A1b A4a by blast
 
lemma "\<lfloor>rigidPred \<P>\<rfloor>" 
  using A4a A4b by blast (** @{term "\<P>"} is therefore rigid*)
    
lemma True nitpick[satisfy] oops (**model found: so far all axioms A1-4 consistent*)
    
(** Nitpick cannot find countermodel for \emph{Modal collapse} (a proof of MC will have to wait until we introduce S5 axioms)*)
lemma "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>" (*nitpick*) oops
    
subsubsection \<open>Theorems\<close>
(** Remark: Essence is defined here (and in Fitting's variant) in the version of Scott; G\"odel's original version leads to the inconsistency
 reported in @{cite "C55,C60"}*)

abbreviation essenceOf::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>,\<zero>\<rangle>" ("\<E>") where
  "\<E> Y x \<equiv> (Y x) \<^bold>\<and> (\<^bold>\<forall>Z. Z x \<^bold>\<rightarrow> Y \<Rrightarrow> Z)"   
abbreviation beingIdenticalTo::"\<zero>\<Rightarrow>\<up>\<langle>\<zero>\<rangle>" ("id") where
  "id x  \<equiv> (\<lambda>y. y\<^bold>\<approx>x)"  (** note that \emph{id} is a rigid predicate*)  

(** Theorem 11.20 - Informal Proposition 5 *)
theorem GodIsEssential: "\<lfloor>\<^bold>\<forall>x. G x \<^bold>\<rightarrow> (\<E> G x)\<rfloor>" using A1b A4a by metis
    
(** Theorem 11.21 *)
theorem "\<lfloor>\<^bold>\<forall>x. G* x \<^bold>\<rightarrow> (\<E> G* x)\<rfloor>" using A4a by meson             
    
(** Theorem 11.22 - Something can have only one essence: *)
theorem "\<lfloor>\<^bold>\<forall>X Y z. (\<E> X z \<^bold>\<and> \<E> Y z) \<^bold>\<rightarrow> (X \<Rrightarrow> Y)\<rfloor>" by meson  
  
(** Theorem 11.23 - An essence is a complete characterization of an individual: *)
theorem EssencesCharacterizeCompletely: "\<lfloor>\<^bold>\<forall>X y. \<E> X y \<^bold>\<rightarrow> (X \<Rrightarrow> (id y))\<rfloor>"
proof (rule ccontr)
  (*<*)
  assume "\<not> \<lfloor>\<^bold>\<forall>X y. \<E> X y \<^bold>\<rightarrow> (X \<Rrightarrow> (id y))\<rfloor>"
  hence "\<exists>w. \<not>(( \<^bold>\<forall>X y. \<E> X y \<^bold>\<rightarrow> X \<Rrightarrow> id y) w)" by simp
  then obtain w where "\<not>(( \<^bold>\<forall>X y. \<E> X y \<^bold>\<rightarrow> X \<Rrightarrow> id y) w)" ..
  hence "(\<^bold>\<exists>X y. \<E> X y \<^bold>\<and> \<^bold>\<not>(X \<Rrightarrow> id y)) w" by simp
  hence "\<exists>X y. \<E> X y w \<and> (\<^bold>\<not>(X \<Rrightarrow> id y)) w" by simp
  then obtain P where "\<exists>y. \<E> P y w \<and> (\<^bold>\<not>(P \<Rrightarrow> id y)) w" ..
  then obtain a where 1: "\<E> P a w \<and> (\<^bold>\<not>(P \<Rrightarrow> id a)) w" ..
  hence 2: "\<E> P a w" by (rule conjunct1)
  from 1 have "(\<^bold>\<not>(P \<Rrightarrow> id a)) w" by (rule conjunct2)
  hence "\<exists>x. \<exists>z. w r x \<and>  existsAt z x \<and> P z x \<and> \<not>(a = z)" by blast
  then obtain w1 where "\<exists>z. w r w1 \<and>  existsAt z w1 \<and> P z w1 \<and> \<not>(a = z)" ..
  then obtain b where 3: "w r w1 \<and>  existsAt b w1 \<and> P b w1 \<and> \<not>(a = b)" ..
  hence "w r w1" by simp
  from 3 have "existsAt b w1" by simp
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
    hence "\<forall>x. \<forall>z. (w r x \<and> existsAt z x \<and> P z x) \<longrightarrow> (\<^bold>\<rightharpoondown>(id b)) z x" by blast
    hence "\<forall>z. (w r w1 \<and> existsAt z w1 \<and> P z w1) \<longrightarrow> (\<^bold>\<rightharpoondown>(id b)) z w1" 
        by (rule allE)
    hence "(w r w1 \<and> existsAt b w1 \<and> P b w1) \<longrightarrow> (\<^bold>\<rightharpoondown>(id b)) b w1" by (rule allE)
    hence  "\<not>(w r w1 \<and> existsAt b w1 \<and> P b w1) \<or> (\<^bold>\<rightharpoondown>(id b)) b w1" by simp
    hence "(\<^bold>\<rightharpoondown>(id b)) b w" using 3 by simp
    hence "\<not>(b=b)" by simp
    thus False by simp
  qed
    (*>*)
qed

(** Definition 11.24 - Necessary Existence (Informal Definition 6): *)  
abbreviation necessaryExistencePred::"\<up>\<langle>\<zero>\<rangle>" ("NE") 
  where "NE x  \<equiv> (\<lambda>w. (\<^bold>\<forall>Y.  \<E> Y x \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E Y) w)"

(** Axiom 11.25 (Informal Axiom 5)*)
axiomatization where 
 A5: "\<lfloor>\<P> NE\<rfloor>"
 
lemma True nitpick[satisfy] oops (** model found: so far all axioms consistent*)
 
(** Theorem 11.26 (Informal Proposition 7) - Possibilist existence of God implies necessary actualist existence: *) 
theorem GodExistenceImpliesNecExistence: "\<lfloor>\<^bold>\<exists> G \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<rfloor>"
proof -
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
      (*>*)
qed
  
(** We postulate semantic frame conditions for some modal logics. Taken together, reflexivity, transitivity and symmetry
 make for an equivalence relation and therefore an \emph{S5} logic (via \emph{Sahlqvist correspondence}).
 We prefer to postulate them individually here in order to get more detailed information about their relevance 
 in the proofs presented below.*)
axiomatization where
 refl: "reflexive aRel" and
 tran: "transitive aRel" and
 symm: "symmetric aRel"
 
lemma True nitpick[satisfy] oops (** model found: axioms still consistent*)
(** Using an \emph{S5} logic, \emph{modal collapse} (@{text "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>"}) is actually valid (see `More Objections' some pages below)*)
    
(** We prove some useful inference rules:*)    
lemma modal_distr: "\<lfloor>\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<psi>)\<rfloor> \<Longrightarrow> \<lfloor>(\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<psi>)\<rfloor>" by blast
lemma modal_trans: "(\<lfloor>\<phi> \<^bold>\<rightarrow> \<psi>\<rfloor> \<and> \<lfloor>\<psi> \<^bold>\<rightarrow> \<chi>\<rfloor>) \<Longrightarrow> \<lfloor>\<phi> \<^bold>\<rightarrow> \<chi>\<rfloor>" by simp

(** Theorem 11.27 - Informal Proposition 8. Note that only symmetry and transitivity for the accessibility relation are used.*) 
theorem possExistenceImpliesNecEx: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> G \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<rfloor>" (**local consequence*)
proof -
  have "\<lfloor>\<^bold>\<exists> G \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<rfloor>" using GodExistenceImpliesNecExistence 
    by simp (** follows from Axioms 11.11, 11.25 and 11.3B*)
  hence "\<lfloor>\<^bold>\<box>(\<^bold>\<exists> G \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G)\<rfloor>" using NEC by simp
  hence 1: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> G \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<rfloor>" by (rule modal_distr)
  have 2: "\<lfloor>\<^bold>\<diamond>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<rfloor>" using symm tran by metis (**frame conditions*)
  from 1 2 have "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> G \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<rfloor> \<and> \<lfloor>\<^bold>\<diamond>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<rfloor>" by simp
  thus ?thesis by (rule modal_trans)
qed

lemma T4: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> G\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<rfloor>" using possExistenceImpliesNecEx 
    by (rule localImpGlobalCons)  (** global consequence*)
  
(** Corollary 11.28 - Necessary (actualist) existence of God (for both definitions); reflexivity is still not used: *)    
lemma GodNecExists: "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<rfloor>" using T3 T4 by metis    
lemma God_starNecExists: "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G*\<rfloor>" 
  using GodNecExists GodDefsAreEquivalent by simp
    

subsubsection \<open>Monotheism\<close>
 
(** Monotheism for non-normal models (with Leibniz equality) follows directly from God having all and only positive properties: *)
theorem Monotheism_LeibnizEq: "\<lfloor>\<^bold>\<forall>x. G x \<^bold>\<rightarrow> (\<^bold>\<forall>y. G y \<^bold>\<rightarrow> (x  \<^bold>\<approx>\<^sup>L y))\<rfloor>" 
  using GodDefsAreEquivalent by simp
    
(** Monotheism for normal models is trickier. We need to consider some previous results (p. 162):*)
    
lemma GodExistenceIsValid: "\<lfloor>\<^bold>\<exists>\<^sup>E G\<rfloor>" using GodNecExists refl
  by auto (**reflexivity is now required by the solver*)
        
(** Proposition 11.29: *)
theorem Monotheism_normalModel: "\<lfloor>\<^bold>\<exists>x.\<^bold>\<forall>y. G y \<^bold>\<leftrightarrow> x \<^bold>\<approx> y\<rfloor>"
proof -
  (*<*)
{
  fix w 
  have "\<lfloor>\<^bold>\<exists>\<^sup>E G\<rfloor>" using GodExistenceIsValid by simp (** follows from corollary 11.28*)
  hence "(\<^bold>\<exists>\<^sup>E G) w" by (rule allE)       
  then obtain g where 1: "existsAt g w \<and> G g w" ..
  hence 2: "\<E> G g w" using GodIsEssential by blast (**follows from ax. 11.11/11.3B*)
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
      hence "\<forall>x. w r x \<longrightarrow> ((\<forall>z. (existsAt z x \<and> G z x) \<longrightarrow> z = y))" by auto
      hence "w r w \<longrightarrow> ((\<forall>z. (existsAt z w \<and> G z w) \<longrightarrow> z = y))" by (rule allE)
      hence "\<forall>z. (w r w \<and> existsAt z w \<and> G z w) \<longrightarrow> z = y" by auto
      hence 4: "(w r w \<and> existsAt g w \<and> G g w) \<longrightarrow> g = y" by (rule allE)
      have "w r w" using refl 
        by simp (** using frame reflexivity (Axiom M)*)
      hence  "w r w \<and> (existsAt g w \<and> G g w)" using 1 by (rule conjI)
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
      (*>*)
qed
  
(**Corollary 11.30: *)
lemma GodImpliesExistence: "\<lfloor>\<^bold>\<forall>x. G x \<^bold>\<rightarrow> E! x\<rfloor>" 
  using GodExistenceIsValid Monotheism_normalModel by metis

subsubsection \<open>Positive Properties are Necessarily Instantiated\<close>
  
lemma PosPropertiesNecExist: "\<lfloor>\<^bold>\<forall>Y. \<P> Y \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E Y\<rfloor>" using GodNecExists A4a
  by meson (**proposition 11.31: follows from corollary 11.28 and axiom A4a*)
 
    
subsubsection \<open>More Objections\<close>
(** Fitting discusses the objection raised by Sobel @{cite "sobel2004logic"}, who argues that G\"odel's axiom system
 is too strong: it implies that whatever is the case is so necessarily, i.e. the modal system collapses (@{text "\<phi> \<longrightarrow> \<box>\<phi>"}).
 The \emph{modal collapse} has been philosophically interpreted as implying the absence of free will.*)

(** We start by proving an useful FOL lemma:*)  
lemma useful: "(\<forall>x. \<phi> x \<longrightarrow> \<psi>) \<Longrightarrow> ((\<exists>x. \<phi> x) \<longrightarrow> \<psi>)" by simp
    
(** In the context of our S5 axioms, the \emph{modal collapse} becomes valid (pp. 163-4): *)     
lemma ModalCollapse: "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>"
proof -
  {
  fix w
   {
    fix Q
    have "(\<^bold>\<forall>x. G x \<^bold>\<rightarrow> (\<E> G x)) w" using GodIsEssential 
      by (rule allE) (** follows from Axioms 11.11 and 11.3B *)
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
   }
  hence "(\<^bold>\<forall>\<Phi>. \<Phi> \<^bold>\<rightarrow> \<^bold>\<box> \<Phi>) w" by (rule allI)
  }
  thus ?thesis by (rule allI)
qed

(*<*)
end
(*>*)