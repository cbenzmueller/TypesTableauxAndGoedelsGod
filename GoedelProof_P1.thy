(*<*)
theory GoedelProof_P1
imports HOML_int
begin
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 3,  atoms e = a b c d]
sledgehammer_params[verbose=true]
(*>*)  

section \<open>G\"odel's Argument, Formally\<close>

(**
 "G\"odel's particular version of the argument is a direct descendent of that of Leibniz, which in turn derives
  from one of Descartes. These arguments all have a two-part structure: prove God's existence is necessary,
  if possible; and prove God's existence is possible." @{cite "Fitting"} p. 138.*) 

subsection \<open>Part I - God's Existence is Possible\<close>

(** We divide G\"odel's Argument as presented in this textbook (Chapter 11) in two parts. For the first one, while Leibniz provides
  some kind of proof for the compatibility of all perfections, G\"odel goes on to prove an analogous result:
 (T1) "Every positive property is possibly instantiated", which together with (T2) "God is a positive property"
  directly implies the conclusion. In order to prove T1 G\"odel assumes A2: "Any property entailed by a positive property is positive".*)
(** We are currently contemplating a follow-up analysis of the philosophical implications of these axioms,
 which may encompass some criticism of the notion of property entailment used by G\"odel throughout the argument.*)
  
subsubsection \<open>General Definitions\<close>
                
abbreviation existencePredicate::"\<up>\<langle>\<zero>\<rangle>" ("E!") 
  where "E! x  \<equiv> \<lambda>w. (\<^bold>\<exists>\<^sup>Ey. y\<^bold>\<approx>x) w" (**existence predicate in the object-language*)

lemma "E! x w \<longleftrightarrow> existsAt x w" 
  by simp (**safety check: correctly matches its meta-logical counterpart*)

consts positiveProperty::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>" ("\<P>") (** Positiveness/Perfection *)
  
(** Definitions of God (later shown to be equivalent under axiom @{text "A1b"}): *)    
abbreviation God::"\<up>\<langle>\<zero>\<rangle>" ("G") where "G \<equiv> (\<lambda>x. \<^bold>\<forall>Y. \<P> Y \<^bold>\<rightarrow> Y x)"
abbreviation God_star::"\<up>\<langle>\<zero>\<rangle>" ("G*") where "G* \<equiv> (\<lambda>x. \<^bold>\<forall>Y. \<P> Y \<^bold>\<leftrightarrow> Y x)"
  
(** Definitions needed to formalise @{text "A3"}: *)
abbreviation appliesToPositiveProps::"\<up>\<langle>\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>\<rangle>" ("pos") where
  "pos Z \<equiv>  \<^bold>\<forall>X. Z X \<^bold>\<rightarrow> \<P> X"
abbreviation intersectionOf::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>,\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>\<rangle>" ("intersec") where
  "intersec X Z \<equiv>  \<^bold>\<box>(\<^bold>\<forall>x.(X x \<^bold>\<leftrightarrow> (\<^bold>\<forall>Y. (Z Y) \<^bold>\<rightarrow> (Y x))))" (** quantifier is possibilist*)
abbreviation Entailment::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>,\<up>\<langle>\<zero>\<rangle>\<rangle>" (infix "\<Rrightarrow>" 60) where
  "X \<Rrightarrow> Y \<equiv>  \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. X z \<^bold>\<rightarrow> Y z)"

subsubsection \<open>Axioms\<close>
    
axiomatization where
  A1a:"\<lfloor>\<^bold>\<forall>X. \<P> (\<^bold>\<rightharpoondown>X) \<^bold>\<rightarrow> \<^bold>\<not>(\<P> X) \<rfloor>" and      (** Axiom 11.3A *)
  A1b:"\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<P> (\<^bold>\<rightharpoondown>X)\<rfloor>" and       (** Axiom 11.3B *)
  A2: "\<lfloor>\<^bold>\<forall>X Y. (\<P> X \<^bold>\<and> (X \<Rrightarrow> Y)) \<^bold>\<rightarrow> \<P> Y\<rfloor>" and   (** Axiom 11.5 *)
  A3: "\<lfloor>\<^bold>\<forall>Z X. (pos Z \<^bold>\<and> intersec X Z) \<^bold>\<rightarrow> \<P> X\<rfloor>" (** Axiom 11.10 *)

lemma True nitpick[satisfy] oops       (** Model found: axioms are consistent*)
    
lemma "\<lfloor>D\<rfloor>"  using A1a A1b A2 by blast (** axioms already imply @{text "D"} axiom *)
lemma "\<lfloor>D\<rfloor>" using A1a A3 by metis

subsubsection \<open>Theorems\<close>
    
lemma "\<lfloor>\<^bold>\<exists>X. \<P> X\<rfloor>" using A1b by auto
lemma "\<lfloor>\<^bold>\<exists>X. \<P> X \<^bold>\<and>  \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X\<rfloor>" using A1a A1b A2 by metis
    
(** Being self-identical is a positive property: *)
lemma "\<lfloor>(\<^bold>\<exists>X. \<P> X \<^bold>\<and>  \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X) \<^bold>\<rightarrow> \<P> (\<lambda>x w. x = x)\<rfloor>" using A2 by fastforce
    
(** Proposition 11.6 *)
lemma "\<lfloor>(\<^bold>\<exists>X. \<P> X) \<^bold>\<rightarrow> \<P> (\<lambda>x w. x = x)\<rfloor>" using A2 by fastforce
    
lemma "\<lfloor>\<P> (\<lambda>x w. x = x)\<rfloor>" using A1b A2  by blast
lemma "\<lfloor>\<P> (\<lambda>x w. x = x)\<rfloor>" using A3 by metis
                                
(** Being non-self-identical is a negative property:*)
lemma "\<lfloor>(\<^bold>\<exists>X. \<P> X  \<^bold>\<and> \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X) \<^bold>\<rightarrow>  \<P> (\<^bold>\<rightharpoondown> (\<lambda>x w. \<not>x = x))\<rfloor>" 
  using A2 by fastforce
    
lemma "\<lfloor>(\<^bold>\<exists>X. \<P> X) \<^bold>\<rightarrow>  \<P> (\<^bold>\<rightharpoondown> (\<lambda>x w. \<not>x = x))\<rfloor>" using A2 by fastforce
lemma "\<lfloor>(\<^bold>\<exists>X. \<P> X) \<^bold>\<rightarrow>  \<P> (\<^bold>\<rightharpoondown> (\<lambda>x w. \<not>x = x))\<rfloor>" using A3 by metis 

(** Proposition 11.7 *)
lemma "\<lfloor>(\<^bold>\<exists>X. \<P> X) \<^bold>\<rightarrow> \<^bold>\<not>\<P> ((\<lambda>x w. \<not>x = x))\<rfloor>"  using A1a A2 by blast
lemma "\<lfloor>\<^bold>\<not>\<P> (\<lambda>x w. \<not>x = x)\<rfloor>"  using A1a A2 by blast
 
(** Proposition 11.8 (Informal Proposition 1) - Positive properties are possibly instantiated: *)
theorem T1: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X\<rfloor>" using A1a A2 by blast
    
(** Proposition 11.14 - Both defs (@{text "God/God*"}) are equivalent. For improved performance we may prefer to use one or the other: *)
lemma GodDefsAreEquivalent: "\<lfloor>\<^bold>\<forall>x. G x \<^bold>\<leftrightarrow> G* x\<rfloor>" using A1b by force 

(** Proposition 11.15 - Possibilist existence of @{text "God*"} directly implies @{text "A1b"}: *)    
lemma "\<lfloor>\<^bold>\<exists> G* \<^bold>\<rightarrow> (\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<P> (\<^bold>\<rightharpoondown>X))\<rfloor>" by meson

(** Proposition 11.16 - @{text "A3"} implies @{text "P(G)"} (local consequence):  *)   
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

(** Useful lemma: local consequence implies global consequence*)
lemma localImpliesGlobal: "\<lfloor>\<phi> \<^bold>\<rightarrow> \<xi>\<rfloor> \<Longrightarrow> \<lfloor>\<phi>\<rfloor> \<longrightarrow> \<lfloor>\<xi>\<rfloor>" by simp
    
(** @{text "A3"} implies @{text "P(G)"} (as global consequence):*)
lemma A3implT2_global: "\<lfloor>\<^bold>\<forall>Z X. (pos Z \<^bold>\<and> intersec X Z) \<^bold>\<rightarrow> \<P> X\<rfloor> \<longrightarrow> \<lfloor>\<P> G\<rfloor>" 
  using A3implT2_local by (rule localImpliesGlobal) 
  
(** God is a positive property. Note that this theorem can be axiomatized directly 
 (as noted by Dana Scott). We will do so for the second part. *)
theorem T2: "\<lfloor>\<P> G\<rfloor>" using A3implT2_global A3 by simp
  
(** Theorem 11.17 (Informal Proposition 3) - Possibly God exists: *)
theorem T3: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists>\<^sup>E G\<rfloor>"  using T1 T2 by simp

(*<*)
end
(*>*)