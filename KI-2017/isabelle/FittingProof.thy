(*<*)
theory FittingProof  
imports IHOML
begin
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 4,  atoms e = a b c d]
sledgehammer_params[verbose=true]
(*>*)
  
section \<open>Fitting's Variant\<close>
  
(**In this section we consider Fitting's solution to the objections raised in his discussion of G\"odel's Argument (@{cite "Fitting"}, pp. 164-9), 
especially the problem of modal collapse, which has been metaphysically interpreted as implying a rejection of free will.
In G\"odel variant, positiveness and essence were thought of as predicates applying to \emph{intensional} properties and
correspondingly formalized using intensional types for their arguments (@{text "\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>"} and @{text "\<up>\<langle>\<up>\<langle>\<zero>\<rangle>,\<zero>\<rangle>"} respectively).
In this variant, Fitting chooses to reformulate these definitions using \emph{extensional} types instead (@{text "\<up>\<langle>\<langle>\<zero>\<rangle>\<rangle>"} and @{text "\<up>\<langle>\<langle>\<zero>\<rangle>,\<zero>\<rangle>"})
and makes the corresponding adjustments to the rest of the argument (to ensure type correctness).
This has some philosophical repercusions, e.g. while we could say before that honesty (as concept) was a
positive property, we can now only talk of its extension at some world and say of some group of people
that they are honest (and in fact, that they are \emph{necessarily} so, since @{text "\<P>"} has also be proven rigid in this variant).*)

consts Positiveness::"\<up>\<langle>\<langle>\<zero>\<rangle>\<rangle>" ("\<P>")
abbreviation Entailment::"\<up>\<langle>\<langle>\<zero>\<rangle>,\<langle>\<zero>\<rangle>\<rangle>" (infix"\<Rrightarrow>"60)
  where "X \<Rrightarrow> Y \<equiv> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. \<lparr>X z\<rparr> \<^bold>\<rightarrow> \<lparr>Y z\<rparr>)"  
abbreviation essenceOf::"\<up>\<langle>\<langle>\<zero>\<rangle>,\<zero>\<rangle>" ("\<E>") where
    "\<E> Y x \<equiv> \<lparr>Y x\<rparr> \<^bold>\<and> (\<^bold>\<forall>Z::\<langle>\<zero>\<rangle>. \<lparr>Z x\<rparr> \<^bold>\<rightarrow> Y \<Rrightarrow> Z)"
(*<*)
    
(*Remark: The `@{text "\<lparr>_\<rparr>"}' parentheses are used to convert an extensional object into its `rigid'
intensional counterpart (e.g. @{text "\<lparr>\<phi>\<rparr> \<equiv> \<lambda>w. \<phi>"}).*)
abbreviation Existence::"\<up>\<langle>\<zero>\<rangle>" ("E!") where "E! x \<equiv> \<lambda>w. (\<^bold>\<exists>\<^sup>Ey. y\<^bold>\<approx>x) w"
abbreviation God::"\<up>\<langle>\<zero>\<rangle>" ("G") where "G \<equiv> (\<lambda>x. \<^bold>\<forall>Y. \<P> Y \<^bold>\<rightarrow> \<lparr>Y x\<rparr>)"
abbreviation necessaryExistencePredicate :: "\<up>\<langle>\<zero>\<rangle>" ("NE") where
  "NE x  \<equiv> \<lambda>w. (\<^bold>\<forall>Y.  \<E> Y x \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists>\<^sup>Ez. \<lparr>Y z\<rparr>)) w"

axiomatization where
  A1a:"\<lfloor>\<^bold>\<forall>X. \<P> (\<rightharpoondown>X) \<^bold>\<rightarrow> \<^bold>\<not>(\<P> X) \<rfloor>" and
  A1b:"\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<P> (\<rightharpoondown>X)\<rfloor>" and 
  A2: "\<lfloor>\<^bold>\<forall>X Y. (\<P> X \<^bold>\<and> (X \<Rrightarrow> Y)) \<^bold>\<rightarrow> \<P> Y\<rfloor>" and
  T2: "\<lfloor>\<P> \<down>G\<rfloor>"  and                        
  A4a: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<box>(\<P> X)\<rfloor>" and
  A5: "\<lfloor>\<P> \<down>NE\<rfloor>"
  
lemma True nitpick[satisfy] oops (** model found: all axioms consistent*)
        
lemma A4b: "\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<not>(\<P> X)\<rfloor>" using A1a A1b A4a by blast
lemma "\<lfloor>rigidPred \<P>\<rfloor>" using A4a A4b by blast (**@{text "\<P>"} designates rigidly*)
 (*>*)
(**Axioms and theorems remain essentially the same. Particularly (T2) @{text "\<lfloor>\<P> \<down>G\<rfloor>"} and (A5) @{text "\<lfloor>\<P> \<down>NE\<rfloor>"}
work with \emph{relativized} extensional terms now. Fitting's original treatment in @{cite "Fitting"} left several
details unspecified and we had to fill in the gaps by choosing appropriate formalization variants (see @{cite "J35"} for details).*)

theorem T1: "\<lfloor>\<^bold>\<forall>X::\<langle>\<zero>\<rangle>. \<P> X \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ez. \<lparr>X z\<rparr>)\<rfloor>" using A1a A2 by blast 
theorem T3: "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G\<rfloor>" using T1 T2 by simp (**\emph{de re} variant chosen*) 
lemma GodIsEssential: "\<lfloor>\<^bold>\<forall>x. G x \<^bold>\<rightarrow> ((\<E> \<down>\<^sub>1G) x)\<rfloor>" using A1b by metis
    
(** (Possibilist) existence of God implies necessary (actualist) existence.
This theorem could be formalized in two variants (drawing on the \emph{de re/de dicto} distinction).
We prove both of them valid and show how the argument splits in two, culminating in two non-equivalent versions
of the conclusion (one \emph{de re} and the other \emph{de dicto}), both of which are proven valid.*)
lemma GodExImpNecEx1: "\<lfloor>\<^bold>\<exists> \<^bold>\<down>G \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>" proof - (**not shown*)
(*<*)
{
  fix w 
  {
    assume "\<exists>x. G x w"
    then obtain g where 1: "G g w" ..
    hence "NE g w" using A5 by auto
    hence "\<forall>Y. (\<E> Y g w) \<longrightarrow> (\<^bold>\<box>(\<^bold>\<exists>\<^sup>Ez. \<lparr>Y z\<rparr>)) w" by simp
    hence "(\<E> (\<lambda>x. G x w) g w) \<longrightarrow> (\<^bold>\<box>(\<^bold>\<exists>\<^sup>Ez. \<lparr>(\<lambda>x. G x w) z\<rparr>)) w" by (rule allE)
    hence 2: "((\<E> \<down>\<^sub>1G) g w) \<longrightarrow> (\<^bold>\<box>(\<^bold>\<exists>\<^sup>E G)) w" using A4b by meson
    have  "(\<^bold>\<forall>x. G x \<^bold>\<rightarrow> ((\<E> \<down>\<^sub>1G) x)) w" using GodIsEssential by (rule allE)
    hence  "(G g \<^bold>\<rightarrow> ((\<E> \<down>\<^sub>1G) g)) w" by (rule allE)
    hence  "G g w \<longrightarrow> (\<E> \<down>\<^sub>1G) g w" by simp
    from this 1 have 3: "(\<E> \<down>\<^sub>1G) g w" by (rule mp)
    from 2 3 have "(\<^bold>\<box>\<^bold>\<exists>\<^sup>E G) w" by (rule mp)
  }
  hence "(\<exists>x. G x w) \<longrightarrow> (\<^bold>\<box>\<^bold>\<exists>\<^sup>E G) w" by (rule impI)
  hence "((\<^bold>\<exists>x. G x) \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<exists>\<^sup>E G) w" by simp
}
 thus ?thesis by (rule allI) 
qed
(*>*)
  
lemma GodExImpNecEx2: "\<lfloor>\<^bold>\<exists> \<^bold>\<down>G \<^bold>\<rightarrow> ((\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G)\<rfloor>"
  using A4a GodExImpNecEx1 by metis
    
(**In contrast to G\"odel's argument (as presented by Fitting), the following theorems can be proven in logic \emph{K}
 (the \emph{S5} axioms are no longer needed):*)    
lemma T4v1:"\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> \<^bold>\<down>G\<rfloor>\<longrightarrow>\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>" using GodExImpNecEx1 T3 by metis
lemma T4v2:"\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G\<rfloor> \<longrightarrow> \<lfloor>(\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G\<rfloor>"
  using GodExImpNecEx2 by blast
    
(** Necessary Existence of God (\emph{de dicto} and \emph{de re} readings).*)    
lemma GodNecExists_deDicto: "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>" using GodExImpNecEx1 T3 by force
lemma GodNecExists_deRe: "\<lfloor>(\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G\<rfloor>" using T3 T4v2 by blast

(** Modal collapse is countersatisfiable even in \emph{S5}. Note that countermodels with a cardinality of \emph{one} 
for the domain of individuals are found by \emph{Nitpick} (the countermodel shown in Fitting's book has cardinality of \emph{two}).*)
lemma "equivalence aRel \<Longrightarrow> \<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>" nitpick[card 't=1, card i=2] oops (*countermodel*)
(*<*)
end
(*>*)
