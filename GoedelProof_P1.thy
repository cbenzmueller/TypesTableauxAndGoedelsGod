(*<*)
theory GoedelProof_P1
imports HOML_int
begin
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 3,  atoms e = a b c d]
sledgehammer_params[verbose=true]
(*>*)  

section \<open>First Part -  God's existence is possible\<close>
  
subsection \<open>General definitions\<close>
                
abbreviation existencePredicate::"\<up>\<langle>O\<rangle>" ("E!") where "E! x  \<equiv> \<lambda>w. (\<^bold>\<exists>\<^sup>Ey. y\<^bold>\<approx>x) w" 
lemma "E! x w \<longleftrightarrow> existsAt x w" by simp (** Safety check: existence predicate correctly matches its meta-logical counterpart*)

consts positiveProperty::"\<up>\<langle>\<up>\<langle>O\<rangle>\<rangle>" ("\<P>") (** Positiveness/Perfection *)
  
(** Definitions of God (later shown to be equivalent under axiom A1b) *)    
abbreviation God::"\<up>\<langle>O\<rangle>" ("G") where "G \<equiv> (\<lambda>x. \<^bold>\<forall>Y. \<P> Y \<^bold>\<rightarrow> Y x)"
abbreviation God_star::"\<up>\<langle>O\<rangle>" ("G*") where "G* \<equiv> (\<lambda>x. \<^bold>\<forall>Y. \<P> Y \<^bold>\<leftrightarrow> Y x)"
  
(** Definitions needed to formalize A3 *)
abbreviation appliesToPositiveProps::"\<up>\<langle>\<up>\<langle>\<up>\<langle>O\<rangle>\<rangle>\<rangle>" ("pos") where "pos Z \<equiv>  \<^bold>\<forall>X. Z X \<^bold>\<rightarrow> \<P> X"
abbreviation intersectionOf::"\<up>\<langle>\<up>\<langle>O\<rangle>,\<up>\<langle>\<up>\<langle>O\<rangle>\<rangle>\<rangle>" ("intersec") where "intersec X Z \<equiv>  \<^bold>\<box>(\<^bold>\<forall>x.(X x \<^bold>\<leftrightarrow> (\<^bold>\<forall>Y. (Z Y) \<^bold>\<rightarrow> (Y x))))" (* note possibilist quantifier*)

abbreviation Entailment::"\<up>\<langle>\<up>\<langle>O\<rangle>,\<up>\<langle>O\<rangle>\<rangle>" (infix "\<succeq>" 60) where "X \<succeq> Y \<equiv>  \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. X z \<^bold>\<rightarrow> Y z)"

subsection \<open>Axioms for Part I\<close>
    
axiomatization where
  A1a:"\<lfloor>\<^bold>\<forall>X. \<P> (\<^bold>\<rightharpoondown>X) \<^bold>\<rightarrow> \<^bold>\<not>(\<P> X) \<rfloor>" and      (** Axiom 11.3A *)
  A1b:"\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<P> (\<^bold>\<rightharpoondown>X)\<rfloor>" and       (** Axiom 11.3B *)
  A2: "\<lfloor>\<^bold>\<forall>X Y. (\<P> X \<^bold>\<and> (X \<succeq> Y)) \<^bold>\<rightarrow> \<P> Y\<rfloor>" and   (** Axiom 11.5 *)
  A3: "\<lfloor>\<^bold>\<forall>Z X. (pos Z \<^bold>\<and> intersec X Z) \<^bold>\<rightarrow> \<P> X\<rfloor>" (** Axiom 11.10 *)

lemma True nitpick[satisfy] oops (** Axioms are consistent*)
    
(** Axioms imply D: \<^bold>\<forall>\<phi>. \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>" *)
lemma "\<lfloor>D\<rfloor>"  using A1a A1b A2 by blast
lemma "\<lfloor>D\<rfloor>" using A1a A3 by metis

subsection \<open>Theorems\<close>
    
lemma "\<lfloor>\<^bold>\<exists>X. \<P> X\<rfloor>" using A1b by auto
lemma "\<lfloor>\<^bold>\<exists>X. \<P> X \<^bold>\<and>  \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X\<rfloor>" using A1a A1b A2 by metis
    
(** Being self-identical is a positive property *)
lemma "\<lfloor>(\<^bold>\<exists>X. \<P> X \<^bold>\<and>  \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X) \<^bold>\<rightarrow> \<P> (\<lambda>x w. x = x)\<rfloor>"  using A2 by fastforce
    
(** Proposition 11.6 *)
lemma "\<lfloor>(\<^bold>\<exists>X. \<P> X) \<^bold>\<rightarrow> \<P> (\<lambda>x w. x = x)\<rfloor>" using A2 by fastforce
    
lemma "\<lfloor>\<P> (\<lambda>x w. x = x)\<rfloor>" using A1b A2  by blast
lemma "\<lfloor>\<P> (\<lambda>x w. x = x)\<rfloor>" using A3 by metis
                                
(** Being non-self-identical is a negative property*)
lemma "\<lfloor>(\<^bold>\<exists>X. \<P> X  \<^bold>\<and> \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X) \<^bold>\<rightarrow>  \<P> (\<^bold>\<rightharpoondown> (\<lambda>x w. \<not>x = x))\<rfloor>"  using A2 by fastforce
    
lemma "\<lfloor>(\<^bold>\<exists>X. \<P> X) \<^bold>\<rightarrow>  \<P> (\<^bold>\<rightharpoondown> (\<lambda>x w. \<not>x = x))\<rfloor>" using A2 by fastforce
lemma "\<lfloor>(\<^bold>\<exists>X. \<P> X) \<^bold>\<rightarrow>  \<P> (\<^bold>\<rightharpoondown> (\<lambda>x w. \<not>x = x))\<rfloor>"  using A3 by metis 

(** Proposition 11.7 *)
lemma "\<lfloor>(\<^bold>\<exists>X. \<P> X) \<^bold>\<rightarrow> \<^bold>\<not>\<P> ((\<lambda>x w. \<not>x = x))\<rfloor>"  using A1a A2 by blast
lemma "\<lfloor>\<^bold>\<not>\<P> (\<lambda>x w. \<not>x = x)\<rfloor>"  using A1a A2 by blast
 
(** Proposition 11.8 (Informal Proposition 1) - Positive properties are possibly instantiated *)
theorem T1: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X\<rfloor>" using A1a A2 by blast  (* invalid when using concept containment 2, 3 & 4 *)
    
(** Proposition 11.14 - Both defs (God/God* ) are equivalent. For improved performance we may prefer to use one or the other *)
lemma GodDefsAreEquivalent: "\<lfloor>\<^bold>\<forall>x. G x \<^bold>\<leftrightarrow> G* x\<rfloor>" using A1b by force 

(** Proposition 11.15 - (possibilist) existence of God* directly implies A1b *)    
lemma "\<lfloor>\<^bold>\<exists> G* \<^bold>\<rightarrow> (\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<P> (\<^bold>\<rightharpoondown>X))\<rfloor>" by meson

(** Proposition 11.16 - A3 implies \<P> G (local consequence)  *)   
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

(** A3 implies \<P> G (as global consequence)*)
lemma A3implT2_global: "\<lfloor>\<^bold>\<forall>Z X. (pos Z \<^bold>\<and> intersec X Z) \<^bold>\<rightarrow> \<P> X\<rfloor> \<longrightarrow> \<lfloor>\<P> G\<rfloor>" using A3implT2_local by smt (* TODO replace smt*)
  
(** God is a positive property. Note Scott's proposal of axiomatizing this (replacing A3) *)
theorem T2: "\<lfloor>\<P> G\<rfloor>" using A3implT2_global A3 by simp
  
(** Theorem 11.17 (Informal Proposition 3) - Possibly God exists *)
theorem T3: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists>\<^sup>E G\<rfloor>"  using T1 T2 by simp

end