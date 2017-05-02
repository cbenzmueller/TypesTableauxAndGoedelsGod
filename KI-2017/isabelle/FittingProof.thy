(*<*)
theory FittingProof  
imports IHOML
begin
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 4,  atoms e = a b c d]
sledgehammer_params[verbose=true]
(*>*)
  
section \<open>Fitting's Variant\<close>
  
(**In this section we consider Fitting's solution to the objections raised in his discussion of G\"odel's Argument pp. 164-9, 
especially the problem of \emph{modal collapse}, which has been metaphysically interpreted as implying a rejection of free will.
Since we are generally commited to the existence of free will (in a pre-theoretical sense), such a result is
philosophically unappealing and rather seen as a problem in the argument's formalisation.*)
(*This part of the book still leaves several details unspecified and the reader is thus compelled to fill in the gaps.
As a result, we came across some premises and theorems allowing for different formalisations and therefore leading to disparate implications.
Only some of those cases are shown here for illustrative purposes. The options we have chosen here are such that
they indeed validate the argument (and we assume that they correspond to Fitting's intention.*)
  
(**Reminder: The `@{text "\<lparr>_\<rparr>"}' parentheses are used to convert an extensional object into its `rigid'
intensional counterpart (e.g. @{text "\<lparr>\<phi>\<rparr> \<equiv> \<lambda>w. \<phi>"}).*)
  
abbreviation Entailment::"\<up>\<langle>\<langle>\<zero>\<rangle>,\<langle>\<zero>\<rangle>\<rangle>" (infix"\<Rrightarrow>"60)
  where "X \<Rrightarrow> Y \<equiv> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. \<lparr>X z\<rparr> \<^bold>\<rightarrow> \<lparr>Y z\<rparr>)"  
consts Positiveness::"\<up>\<langle>\<langle>\<zero>\<rangle>\<rangle>" ("\<P>")
abbreviation Existence::"\<up>\<langle>\<zero>\<rangle>" ("E!") where "E! x \<equiv> \<lambda>w. (\<^bold>\<exists>\<^sup>Ey. y\<^bold>\<approx>x) w"
abbreviation God::"\<up>\<langle>\<zero>\<rangle>" ("G") where "G \<equiv> (\<lambda>x. \<^bold>\<forall>Y. \<P> Y \<^bold>\<rightarrow> \<lparr>Y x\<rparr>)"
  
subsection \<open>Part I - God's Existence is Possible\<close>  
  
axiomatization where
  A1a:"\<lfloor>\<^bold>\<forall>X. \<P> (\<rightharpoondown>X) \<^bold>\<rightarrow> \<^bold>\<not>(\<P> X) \<rfloor>" and        (** axiom 11.3A *)
  A1b:"\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<P> (\<rightharpoondown>X)\<rfloor>" and         (** axiom 11.3B *)
  A2: "\<lfloor>\<^bold>\<forall>X Y. (\<P> X \<^bold>\<and> (X \<Rrightarrow> Y)) \<^bold>\<rightarrow> \<P> Y\<rfloor>" and  (** axiom 11.5 *)
  T2: "\<lfloor>\<P> \<down>G\<rfloor>"                               (** proposition 11.16 (modified)*)
lemma True nitpick[satisfy] oops (** model found: axioms are consistent*)
    
(** \emph{T1} Positive properties are possibly instantiated*)    
theorem T1: "\<lfloor>\<^bold>\<forall>X::\<langle>\<zero>\<rangle>. \<P> X \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ez. \<lparr>X z\<rparr>)\<rfloor>" using A1a A2 by blast 
(** \emph{T3} (God exists possibly) can be formalised in two different ways, using a \emph{de re} or a \emph{de dicto} reading.*)
theorem T3_deRe: "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G\<rfloor>" using T1 T2 by simp 
theorem T3_deDicto: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>" nitpick oops (**countersatisfiable: not used*)      
    
subsection \<open>Part II - God's Existence is Necessary if Possible\<close>

axiomatization where
      A4a: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<box>(\<P> X)\<rfloor>"      (** axiom 11.11 *)
lemma A4b: "\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<not>(\<P> X)\<rfloor>" using A1a A1b A4a by blast
    
lemma True nitpick[satisfy] oops (** model found: so far all axioms consistent*)
lemma "\<lfloor>rigidPred \<P>\<rfloor>" using A4a A4b by blast (**@{text "\<P>"} designates rigidly*)
    
abbreviation essenceOf::"\<up>\<langle>\<langle>\<zero>\<rangle>,\<zero>\<rangle>" ("\<E>") where
  "\<E> Y x \<equiv> \<lparr>Y x\<rparr> \<^bold>\<and> (\<^bold>\<forall>Z::\<langle>\<zero>\<rangle>. \<lparr>Z x\<rparr> \<^bold>\<rightarrow> Y \<Rrightarrow> Z)"
theorem GodIsEssential: "\<lfloor>\<^bold>\<forall>x. G x \<^bold>\<rightarrow> ((\<E> \<down>\<^sub>1G) x)\<rfloor>" using A1b by metis
    
abbreviation necessaryExistencePredicate :: "\<up>\<langle>\<zero>\<rangle>" ("NE") where
  "NE x  \<equiv> \<lambda>w. (\<^bold>\<forall>Y.  \<E> Y x \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists>\<^sup>Ez. \<lparr>Y z\<rparr>)) w"
  
axiomatization where A5: "\<lfloor>\<P> \<down>NE\<rfloor>"    
lemma True nitpick[satisfy] oops (** model found: so far all axioms consistent*)
    
(** Theorem 11.26 (Informal Proposition 7) - (possibilist) existence of God implies necessary (actualist) existence.
This theorem can be formalized in two ways. Both of them are proven valid:*)
theorem GodExImpNecEx_v1: "\<lfloor>\<^bold>\<exists> \<^bold>\<down>G \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>" proof - (**not shown here*)
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
qed (*>*)
  
theorem GodExImpNecEx_v2: "\<lfloor>\<^bold>\<exists> \<^bold>\<down>G \<^bold>\<rightarrow> ((\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G)\<rfloor>"
  using A4a GodExImpNecEx_v1 by metis (**can be proven by automated tools*)
    
(** In contrast to G\"odel's argument (as presented by Fitting), the following theorems can be proven in logic \emph{K}
 (the \emph{S5} axioms are no longer needed):*)
theorem possExImpNecEx_v1: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> \<^bold>\<down>G \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>"
  using GodExImpNecEx_v1 T3_deRe by metis
theorem possExImpNecEx_v2: "\<lfloor>(\<lambda>X.\<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G \<^bold>\<rightarrow> (\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G\<rfloor>"
  using GodExImpNecEx_v2 by blast

lemma T4_v1:"\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> \<^bold>\<down>G\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>" using possExImpNecEx_v1 by simp
lemma T4_v2:"\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G\<rfloor>\<longrightarrow>\<lfloor>(\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G\<rfloor>" using possExImpNecEx_v2 by simp
    
subsection \<open>Conclusion (\emph{De Re} and \emph{De Dicto} Reading)\<close>        
    
(** Version I - Necessary Existence of God (\emph{de dicto}): *)    
lemma GodNecExists_v1: "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>"
  using GodExImpNecEx_v1 T3_deRe by fastforce (** corollary 11.28*)
lemma "\<lfloor>\<^bold>\<box>(\<lambda>X. \<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G\<rfloor>"
  using GodNecExists_v1 by simp (**\emph{de dicto} shown here explicitly*)
    
(** Version II - Necessary Existence of God (\emph{de re}) *)    
lemma GodNecExists_v2: "\<lfloor>(\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G\<rfloor>"
  using T3_deRe T4_v2 by blast

subsection \<open>Modal Collapse\<close>
(** Modal collapse is countersatisfiable even in \emph{S5}. Note that countermodels with a cardinality of one 
for the domain of individuals are found by \emph{Nitpick} (the countermodel shown in the book has cardinality of two).*)
    
axiomatization where S5: "equivalence aRel" (**\emph{S5} axioms assumed *)
lemma "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>" nitpick[card 't=1, card i=2] oops (**countermodel*)
(*<*)
end
(*>*)
