(*<*)
theory AndersonProof  
imports HOML_int
begin
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 4,  atoms e = a b c d]
sledgehammer_params[verbose=true]
(*>*)
  
section \<open>Anderson's Alternative\<close>
  
(**In this last section we consider Anderson's Alternative to the objections previously shown, as exposed in the last
part of the textbook (pp. 169-171)*)
  
subsection \<open>General Definitions\<close>
 
abbreviation existencePredicate::"\<up>\<langle>\<zero>\<rangle>" ("E!") 
  where "E! x  \<equiv> \<lambda>w. (\<^bold>\<exists>\<^sup>Ey. y\<^bold>\<approx>x) w"
  
consts positiveProperty::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>" ("\<P>")
  
(** Godlike, Anderson Version (Definition 11.33) *)    
abbreviation God::"\<up>\<langle>\<zero>\<rangle>" ("G\<^sup>A") where "G\<^sup>A \<equiv> \<lambda>x. \<^bold>\<forall>Y. (\<P> Y) \<^bold>\<leftrightarrow> \<^bold>\<box>(Y x)"
  
abbreviation Entailment::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>,\<up>\<langle>\<zero>\<rangle>\<rangle>" (infix "\<Rrightarrow>" 60) where
  "X \<Rrightarrow> Y \<equiv>  \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. X z \<^bold>\<rightarrow> Y z)"
  
subsection \<open>Part I - God's Existence is Possible\<close>  
  
axiomatization where
  A1a:"\<lfloor>\<^bold>\<forall>X. \<P> (\<^bold>\<rightharpoondown>X) \<^bold>\<rightarrow> \<^bold>\<not>(\<P> X) \<rfloor>" and          (** Axiom 11.3A *)
  A2: "\<lfloor>\<^bold>\<forall>X Y. (\<P> X \<^bold>\<and> (X \<Rrightarrow> Y)) \<^bold>\<rightarrow> \<P> Y\<rfloor>" and   (** Axiom 11.5 *)
  T2: "\<lfloor>\<P> G\<^sup>A\<rfloor>"                                 (** Proposition 11.16 *)
        
lemma True nitpick[satisfy] oops (** Model found: axioms are consistent*)
    
theorem T1: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X\<rfloor>" 
  using A1a A2 by blast  (** Positive properties are possibly instantiated*)  
theorem T3: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" using T1 T2 by simp  (** God exists possibly *)  
    
    
subsection \<open>Part II - God's Existence is Necessary if Possible\<close>
        
(** @{text "\<P>"} now satisfies only one of the stability conditions (p. 124). But since the argument uses an @{text "S5"} logic, 
the other stability condition is implied. Therefore @{text "\<P>"} becomes rigid. *)
axiomatization where
  A4a: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<box>(\<P> X)\<rfloor>"      (** Axiom 11.11 *)
      
(** Axiomatizing semantic frame conditions for different modal logics (via \emph{Sahlqvist correspondence}).
 All axioms together imply an @{term "S5"} logic.*)
axiomatization where
 refl: "reflexive aRel" and
 tran: "transitive aRel" and
 symm: "symmetric aRel"
 
lemma True nitpick[satisfy] oops (** Model found: so far all axioms consistent*)
 
abbreviation rigidPred::"('t\<Rightarrow>io)\<Rightarrow>io" where
 "rigidPred \<tau> \<equiv> (\<lambda>\<beta>. \<^bold>\<box>((\<lambda>z. \<beta> \<^bold>\<approx> z) \<^bold>\<down>\<tau>)) \<^bold>\<down>\<tau>"

lemma A4b: "\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<not>(\<P> X)\<rfloor>" 
  using A4a symm by auto (**note only symmetry is needed (@{term "B"} axiom) *)
lemma "\<lfloor>rigidPred \<P>\<rfloor>" 
  using A4a A4b by blast (**@{term "\<P>"} is therefore rigid in a @{term "B"} logic*)
  
    
subsubsection \<open>Theorems\<close>

(** Essence, Anderson Version (Definition 11.34)*)
abbreviation essenceOf::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>,\<zero>\<rangle>" ("\<E>\<^sup>A") where
  "\<E>\<^sup>A Y x \<equiv> (\<^bold>\<forall>Z. \<^bold>\<box>(Z x) \<^bold>\<leftrightarrow> Y \<Rrightarrow> Z)"

      
(** Necessary Existence, Anderson Version (Definition 11.35) *)  
abbreviation necessaryExistencePred::"\<up>\<langle>\<zero>\<rangle>" ("NE\<^sup>A") 
  where "NE\<^sup>A x  \<equiv> (\<lambda>w. (\<^bold>\<forall>Y.  \<E>\<^sup>A Y x \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E Y) w)"
  
(*abbreviation beingIdenticalTo::"\<zero>\<Rightarrow>\<up>\<langle>\<zero>\<rangle>" ("id") where
  "id x  \<equiv> (\<lambda>y. y\<^bold>\<approx>x)"  note that @{term "id"} is a rigid predicate*)  
    
(* Theorem 2. from Anderson (1990)
If something is God-like, then the property of being God-like
is an essence of that thing.
Proof. Suppose that something g is God-like and let Q be any property of
x. Then Q is positive by the lemma. Now by definition (of "God-like"),
necessarily if Q is positive, anything which is God-like has Q. Hence, if
necessarily Q is positive, then necessarily anything which is God-like has Q
(by modal logic). But by Axiom 4, if Q is positive, necessarily Q is positive.
Therefore, necessarily Q is positive. So necessarily anything which is God-
like has Q - i.e., the property of being God-like entails Q. Thus we have
shown that any property of g is entailed by the property of being God-like.
So, by the definition of "essence," the property of being God-like is an
essence of anything which has that property.*)
    
(** Theorem 11.36 *)
theorem GodIsEssential: "\<lfloor>\<^bold>\<forall>x. G\<^sup>A x \<^bold>\<rightarrow> (\<E>\<^sup>A G\<^sup>A x)\<rfloor>"
proof -
{
  fix w
  {
    fix g
    {
    assume "G\<^sup>A g w"
    hence "\<forall>Y. (\<P> Y w) \<longleftrightarrow>  (\<^bold>\<box>(Y g)) w" by auto
    then obtain Q where 1: "(\<P> Q w) \<longleftrightarrow>  (\<^bold>\<box>(Q g)) w" ..
     
      (* \<dots>*)  
      have "\<E>\<^sup>A G\<^sup>A g w" sorry
    }
    hence "G\<^sup>A g w  \<longrightarrow> \<E>\<^sup>A G\<^sup>A g w " by (rule impI)
  }
  hence "\<forall>x. G\<^sup>A x w  \<longrightarrow> \<E>\<^sup>A G\<^sup>A x w "  by (rule allI)
}
 thus ?thesis by (rule allI) 
qed

(*proof (rule ccontr)
  assume "\<not>\<lfloor>\<^bold>\<forall>x. G\<^sup>A x \<^bold>\<rightarrow> (\<E>\<^sup>A G\<^sup>A x)\<rfloor>"
  hence "\<exists>w. \<not>((\<^bold>\<forall>x. G\<^sup>A x \<^bold>\<rightarrow> (\<E>\<^sup>A G\<^sup>A x)) w)" by simp
  then obtain w where "\<not>((\<^bold>\<forall>x. G\<^sup>A x \<^bold>\<rightarrow> (\<E>\<^sup>A G\<^sup>A x)) w)" ..
  hence "\<exists>x. G\<^sup>A x w \<and> \<not>(\<E>\<^sup>A G\<^sup>A x w)" by auto
  then obtain g where 1: "G\<^sup>A g w \<and> \<not>(\<E>\<^sup>A G\<^sup>A g w)" ..
  hence 2: "G\<^sup>A g w" by (rule conjunct1)
  from 1 have "\<not>(\<E>\<^sup>A G\<^sup>A g w)" by (rule conjunct2)
  hence "\<not>(\<^bold>\<forall>Z. \<^bold>\<box>(Z g) \<^bold>\<leftrightarrow> G\<^sup>A \<Rrightarrow> Z) w" by auto
  hence "\<exists>Z.\<not>((\<forall>v. (w r v) \<longrightarrow>(Z g v)) \<longleftrightarrow> ((G\<^sup>A \<Rrightarrow> Z) w))" by auto
  then obtain Q where "\<not>((\<forall>v. (w r v) \<longrightarrow>(Q g v)) \<longleftrightarrow> ((G\<^sup>A \<Rrightarrow> Q) w))" ..    
  (* ...*)
  thus False sorry
qed*)


(** Axiom 11.37 (Anderson's Version of 11.25)*)
axiomatization where 
 A5: "\<lfloor>\<P> NE\<^sup>A\<rfloor>"
 
lemma True nitpick[satisfy] oops (** Model found: so far all axioms consistent*)
 
(** Theorem 11.38 - Possibilist existence of God implies necessary actualist existence: *) 
theorem GodExistenceImpliesNecExistence: "\<lfloor>\<^bold>\<exists> G\<^sup>A \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>"
proof -
{
  fix w 
  {
    assume "\<exists>x. G\<^sup>A x w"
    then obtain g where 1: "G\<^sup>A g w" ..
    hence "NE\<^sup>A g w" using A5 by blast                     (** Axiom 11.25*)
    hence "\<forall>Y. (\<E>\<^sup>A Y g w) \<longrightarrow> (\<^bold>\<box>\<^bold>\<exists>\<^sup>E Y) w" by simp
    hence 2: "(\<E>\<^sup>A G\<^sup>A g w) \<longrightarrow> (\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A) w" by (rule allE)
    have  "(\<^bold>\<forall>x. G\<^sup>A x \<^bold>\<rightarrow> (\<E>\<^sup>A G\<^sup>A x)) w" using GodIsEssential
      by (rule allE)     (** GodIsEssential follows from Axioms 11.11 and 11.3B *)
    hence  "(G\<^sup>A g \<^bold>\<rightarrow> (\<E>\<^sup>A G\<^sup>A g)) w" by (rule allE)
    hence  "G\<^sup>A g w \<longrightarrow> \<E>\<^sup>A G\<^sup>A g w"  by blast
    from this 1 have 3: "\<E>\<^sup>A G\<^sup>A g w" by (rule mp)
    from 2 3 have "(\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A) w" by (rule mp)
  }
  hence "(\<exists>x. G\<^sup>A x w) \<longrightarrow> (\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A) w" by (rule impI)
  hence "((\<^bold>\<exists>x. G\<^sup>A x) \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A) w" by simp
}
 thus ?thesis by (rule allI) 
qed
    
(** Some useful rules:*)    
lemma modal_distr: "\<lfloor>\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<psi>)\<rfloor> \<Longrightarrow> \<lfloor>(\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<psi>)\<rfloor>" by blast
lemma modal_trans: "(\<lfloor>\<phi> \<^bold>\<rightarrow> \<psi>\<rfloor> \<and> \<lfloor>\<psi> \<^bold>\<rightarrow> \<chi>\<rfloor>) \<Longrightarrow> \<lfloor>\<phi> \<^bold>\<rightarrow> \<chi>\<rfloor>" by simp

(** Anderson's Version of Theorem 11.27 *) 
theorem possExistenceImpliesNecEx: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> G\<^sup>A \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" (**local consequence*)
proof -
  have "\<lfloor>\<^bold>\<exists> G\<^sup>A \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" using GodExistenceImpliesNecExistence 
    by simp (** follows from Axioms 11.11, 11.25 and 11.3B*)
  hence "\<lfloor>\<^bold>\<box>(\<^bold>\<exists> G\<^sup>A \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A)\<rfloor>" using NEC by simp
  hence 1: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> G\<^sup>A \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" by (rule modal_distr)
  have 2: "\<lfloor>\<^bold>\<diamond>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" using symm tran by metis
  from 1 2 have "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> G\<^sup>A \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor> \<and> \<lfloor>\<^bold>\<diamond>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" by simp
  thus ?thesis by (rule modal_trans)
qed

lemma T4: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> G\<^sup>A\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" using possExistenceImpliesNecEx 
    by simp (** global consequence*)
  
(** Conclusion - Necessary (actualist) existence of God: *)    
lemma GodNecExists: "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" using T3 T4 by metis    
    
subsubsection \<open>Modal Collapse\<close>
  
(** Modal Collapse is countersatisfiable *)
lemma "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>" nitpick oops
     
(*<*)
end
(*>*)