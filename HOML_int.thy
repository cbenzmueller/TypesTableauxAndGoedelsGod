(*<*)
theory HOML_int
imports Relations
begin  
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 3, atoms e = a b c d]
(*>*)

section \<open>Embedding of Higher-Order Modal Logic with Intensional Types\<close>

subsection \<open>Declarations\<close>

  typedecl i                          (** Type for possible worlds*)
  type_synonym io = "(i\<Rightarrow>bool)"       (** Type for formulas whose truth-value is world-dependent*)
  typedecl e  ("O")                   (** Type for individuals*)               
  
  (** Aliases for common unary predicate types *)
  type_synonym ie =     "(i\<Rightarrow>O)"             ("\<up>O")
  type_synonym se =     "(O\<Rightarrow>bool)"          ("\<langle>O\<rangle>")
  type_synonym ise =    "(O\<Rightarrow>io)"           ("\<up>\<langle>O\<rangle>")
  type_synonym sie =    "(\<up>O\<Rightarrow>bool)"        ("\<langle>\<up>O\<rangle>")
  type_synonym isie =   "(\<up>O\<Rightarrow>io)"         ("\<up>\<langle>\<up>O\<rangle>")  
  type_synonym sise =   "(\<up>\<langle>O\<rangle>\<Rightarrow>bool)"     ("\<langle>\<up>\<langle>O\<rangle>\<rangle>")
  type_synonym isise =  "(\<up>\<langle>O\<rangle>\<Rightarrow>io)"      ("\<up>\<langle>\<up>\<langle>O\<rangle>\<rangle>")
  type_synonym sisise=  "(\<up>\<langle>\<up>\<langle>O\<rangle>\<rangle>\<Rightarrow>bool)" ("\<langle>\<up>\<langle>\<up>\<langle>O\<rangle>\<rangle>\<rangle>")
  type_synonym isisise= "(\<up>\<langle>\<up>\<langle>O\<rangle>\<rangle>\<Rightarrow>io)"  ("\<up>\<langle>\<up>\<langle>\<up>\<langle>O\<rangle>\<rangle>\<rangle>")
  type_synonym sse =    "\<langle>O\<rangle>\<Rightarrow>bool"         ("\<langle>\<langle>O\<rangle>\<rangle>")
  type_synonym isse =   "\<langle>O\<rangle>\<Rightarrow>io"          ("\<up>\<langle>\<langle>O\<rangle>\<rangle>")
  
  (** Aliases for common binary relation types *)
  type_synonym see =        "(O\<Rightarrow>O\<Rightarrow>bool)"          ("\<langle>O,O\<rangle>")
  type_synonym isee =       "(O\<Rightarrow>O\<Rightarrow>io)"           ("\<up>\<langle>O,O\<rangle>")
  type_synonym sieie =      "(\<up>O\<Rightarrow>\<up>O\<Rightarrow>bool)"       ("\<langle>\<up>O,\<up>O\<rangle>")
  type_synonym isieie =     "(\<up>O\<Rightarrow>\<up>O\<Rightarrow>io)"        ("\<up>\<langle>\<up>O,\<up>O\<rangle>")
  type_synonym ssese =      "(\<langle>O\<rangle>\<Rightarrow>\<langle>O\<rangle>\<Rightarrow>bool)"     ("\<langle>\<langle>O\<rangle>,\<langle>O\<rangle>\<rangle>")
  type_synonym issese =     "(\<langle>O\<rangle>\<Rightarrow>\<langle>O\<rangle>\<Rightarrow>io)"      ("\<up>\<langle>\<langle>O\<rangle>,\<langle>O\<rangle>\<rangle>")
  type_synonym ssee =       "(\<langle>O\<rangle>\<Rightarrow>O\<Rightarrow>bool)"       ("\<langle>\<langle>O\<rangle>,O\<rangle>")
  type_synonym issee =      "(\<langle>O\<rangle>\<Rightarrow>O\<Rightarrow>io)"        ("\<up>\<langle>\<langle>O\<rangle>,O\<rangle>")
  type_synonym isisee =     "(\<up>\<langle>O\<rangle>\<Rightarrow>O\<Rightarrow>io)"      ("\<up>\<langle>\<up>\<langle>O\<rangle>,O\<rangle>")
  type_synonym isiseise =   "(\<up>\<langle>O\<rangle>\<Rightarrow>\<up>\<langle>O\<rangle>\<Rightarrow>io)"    ("\<up>\<langle>\<up>\<langle>O\<rangle>,\<up>\<langle>O\<rangle>\<rangle>")
  type_synonym isiseisise=  "(\<up>\<langle>O\<rangle>\<Rightarrow>\<up>\<langle>\<up>\<langle>O\<rangle>\<rangle>\<Rightarrow>io)" ("\<up>\<langle>\<up>\<langle>O\<rangle>,\<up>\<langle>\<up>\<langle>O\<rangle>\<rangle>\<rangle>")
  
  consts aRel::"i\<Rightarrow>i\<Rightarrow>bool" (infixr "r" 70)  (** Accessibility relation r *)

subsection {* Definition of logical operators in HOL*}

  abbreviation mnot   :: "io\<Rightarrow>io" ("\<^bold>\<not>_"[52]53)
    where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>(\<phi> w)" 
  abbreviation mand   :: "io\<Rightarrow>io\<Rightarrow>io" (infixr"\<^bold>\<and>"51)
    where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<and>(\<psi> w)"   
  abbreviation mor    :: "io\<Rightarrow>io\<Rightarrow>io" (infixr"\<^bold>\<or>"50)
    where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<or>(\<psi> w)"
  abbreviation xor:: "bool\<Rightarrow>bool\<Rightarrow>bool" (infixr"\<oplus>"50)
    where "\<phi>\<oplus>\<psi> \<equiv>  (\<phi>\<or>\<psi>) \<and> \<not>(\<phi>\<and>\<psi>)" 
  abbreviation mxor   :: "io\<Rightarrow>io\<Rightarrow>io" (infixr"\<^bold>\<oplus>"50)
    where "\<phi>\<^bold>\<oplus>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<oplus>(\<psi> w)"
  abbreviation mimp   :: "io\<Rightarrow>io\<Rightarrow>io" (infixr"\<^bold>\<rightarrow>"49) 
    where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<longrightarrow>(\<psi> w)"  
  abbreviation mequ   :: "io\<Rightarrow>io\<Rightarrow>io" (infixr"\<^bold>\<leftrightarrow>"48)
    where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<longleftrightarrow>(\<psi> w)"  
  abbreviation mforall   :: "('t\<Rightarrow>io)\<Rightarrow>io" ("\<^bold>\<forall>")      
    where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w.\<forall>x. (\<Phi> x w)"
  abbreviation mexists   :: "('t\<Rightarrow>io)\<Rightarrow>io" ("\<^bold>\<exists>") 
    where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x. (\<Phi> x w)"
  abbreviation mforallB  :: "('t\<Rightarrow>io)\<Rightarrow>io" (binder"\<^bold>\<forall>"[8]9)
    where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"  
  abbreviation mexistsB  :: "('t\<Rightarrow>io)\<Rightarrow>io" (binder"\<^bold>\<exists>"[8]9)
    where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>" 
      
subsection {* Definition of actualist quantifiers*}
(** No polymorphic types are used since actualist quantification only makes sense for individuals *)
  
  (** (Meta-logical) existence predicate for restricting domains of quantification *)
  consts Exists::"\<up>\<langle>O\<rangle>" ("existsAt")
    
  abbreviation mforallAct   :: "\<up>\<langle>\<up>\<langle>O\<rangle>\<rangle>" ("\<^bold>\<forall>\<^sup>E")      
    where "\<^bold>\<forall>\<^sup>E\<Phi> \<equiv> \<lambda>w.\<forall>x. (existsAt x w)\<longrightarrow>(\<Phi> x w)"
  abbreviation mexistsAct   :: "\<up>\<langle>\<up>\<langle>O\<rangle>\<rangle>" ("\<^bold>\<exists>\<^sup>E") 
    where "\<^bold>\<exists>\<^sup>E\<Phi> \<equiv> \<lambda>w.\<exists>x. (existsAt x w) \<and> (\<Phi> x w)"
      
  (** Binder notation*)
  abbreviation mforallActB  :: "\<up>\<langle>\<up>\<langle>O\<rangle>\<rangle>" (binder"\<^bold>\<forall>\<^sup>E"[8]9)
    where "\<^bold>\<forall>\<^sup>Ex. \<phi>(x) \<equiv> \<^bold>\<forall>\<^sup>E\<phi>"     
  abbreviation mexistsActB  :: "\<up>\<langle>\<up>\<langle>O\<rangle>\<rangle>" (binder"\<^bold>\<exists>\<^sup>E"[8]9)
    where "\<^bold>\<exists>\<^sup>Ex. \<phi>(x) \<equiv> \<^bold>\<exists>\<^sup>E\<phi>"
      
subsection {* Definition of modal operators*}
    
  abbreviation mbox   :: "io\<Rightarrow>io" ("\<^bold>\<box>_"[52]53)
    where "\<^bold>\<box>\<phi> \<equiv> \<lambda>w.\<forall>v. (w r v)\<longrightarrow>(\<phi> v)"
  abbreviation mdia   :: "io\<Rightarrow>io" ("\<^bold>\<diamond>_"[52]53)
    where "\<^bold>\<diamond>\<phi> \<equiv> \<lambda>w.\<exists>v. (w r v)\<and>(\<phi> v)"

  subsection {* Definition of the ExtensionOf operator *}
(** Embedding in HOL of (world-dependent) atomic formulas whose first argument is relativized *)    
(** ExtensionOf operator is therefore embedded in HOL as a binary operator. Depending on the
types involved we need to define this operator differently to ensure type correctness. *)   

(** (a) \<phi> takes an (intensional) individual concept as argument*)
abbreviation mextIndiv   :: "\<up>\<langle>O\<rangle>\<Rightarrow>\<up>O\<Rightarrow>io" (infix "\<^bold>\<downharpoonleft>" 60)                             
  where "\<phi> \<^bold>\<downharpoonleft>c \<equiv> \<lambda>w. \<phi> (c w) w"
(** (b) \<phi> takes an intensional predicate as argument*)
abbreviation mextPredArg   :: "(('t\<Rightarrow>io)\<Rightarrow>io)\<Rightarrow>('t\<Rightarrow>io)\<Rightarrow>io" (infix "\<^bold>\<down>" 60)
  where "\<phi> \<^bold>\<down>P \<equiv> \<lambda>w. \<phi> (\<lambda>x u. P x w) w"
(** (c) \<phi> takes an extensional predicate as argument*)
abbreviation extPredArg   :: "(('t\<Rightarrow>bool)\<Rightarrow>io)\<Rightarrow>('t\<Rightarrow>io)\<Rightarrow>io" (infix "\<down>" 60)
  where "\<phi> \<down>P \<equiv> \<lambda>w. \<phi> (\<lambda>x. P x w) w"
(** (d) \<phi> takes an extensional predicate as first argument*)
abbreviation extPredArg1   :: "(('t\<Rightarrow>bool)\<Rightarrow>'b\<Rightarrow>io)\<Rightarrow>('t\<Rightarrow>io)\<Rightarrow>'b\<Rightarrow>io" (infix "\<down>\<^sub>1" 60)
  where "\<phi> \<down>\<^sub>1P \<equiv> \<lambda>z. \<lambda>w. \<phi> (\<lambda>x. P x w) z w"
    
    
subsection {* Definition of Equality *}
  
  abbreviation meq    :: "'t\<Rightarrow>'t\<Rightarrow>io" (infix"\<^bold>\<approx>"60) (** normal equality (for all types)*)
    where "x\<^bold>\<approx>y \<equiv> \<lambda>w. x = y"
  abbreviation meqC   :: "\<up>\<langle>\<up>O,\<up>O\<rangle>" (infixr"\<^bold>\<approx>\<^sup>C"52) (** equality for (intensional) individual concepts"*)
    where "x\<^bold>\<approx>\<^sup>Cy \<equiv> \<lambda>w. \<forall>v. (x v) = (y v)"
  abbreviation meqL   :: "\<up>\<langle>O,O\<rangle>" (infixr"\<^bold>\<approx>\<^sup>L"52) (** Leibniz Equality for individuals"*)
    where "x\<^bold>\<approx>\<^sup>Ly \<equiv> \<^bold>\<forall>\<phi>. \<phi>(x)\<^bold>\<rightarrow>\<phi>(y)"
      
subsection {* Miscelaneous *}
  
  abbreviation negpred :: "\<langle>O\<rangle>\<Rightarrow>\<langle>O\<rangle>" ("\<rightharpoondown>_"[52]53) 
    where "\<rightharpoondown>\<Phi> \<equiv> \<lambda>x. \<not>(\<Phi> x)" 
  abbreviation mnegpred :: "\<up>\<langle>O\<rangle>\<Rightarrow>\<up>\<langle>O\<rangle>" ("\<^bold>\<rightharpoondown>_"[52]53) 
    where "\<^bold>\<rightharpoondown>\<Phi> \<equiv> \<lambda>x.\<lambda>w. \<not>(\<Phi> x w)" 
  abbreviation mandpred :: "\<up>\<langle>O\<rangle>\<Rightarrow>\<up>\<langle>O\<rangle>\<Rightarrow>\<up>\<langle>O\<rangle>" (infix "\<^bold>&" 53) 
    where "\<Phi> \<^bold>& \<phi> \<equiv> \<lambda>x.\<lambda>w. (\<Phi> x w) \<and> (\<phi> x w)"


subsection {* Meta-logical predicates*}

 abbreviation valid :: "io\<Rightarrow>bool" ("\<lfloor>_\<rfloor>" [8]) where "\<lfloor>\<psi>\<rfloor> \<equiv>  \<forall>w.(\<psi> w)"
 abbreviation satisfiable :: "io\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sup>s\<^sup>a\<^sup>t" [8]) where "\<lfloor>\<psi>\<rfloor>\<^sup>s\<^sup>a\<^sup>t \<equiv> \<exists>w.(\<psi> w)"
 abbreviation countersatisfiable :: "io\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sup>c\<^sup>s\<^sup>a\<^sup>t" [8]) where "\<lfloor>\<psi>\<rfloor>\<^sup>c\<^sup>s\<^sup>a\<^sup>t \<equiv>  \<exists>w.\<not>(\<psi> w)"
 abbreviation invalid :: "io\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sup>i\<^sup>n\<^sup>v" [8]) where "\<lfloor>\<psi>\<rfloor>\<^sup>i\<^sup>n\<^sup>v \<equiv> \<forall>w.\<not>(\<psi> w)"

section {* Verifying the Embedding *}

 text {* Verifying K Principle and Necessitation *}
 lemma K: "\<lfloor>(\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<psi>)) \<^bold>\<rightarrow> (\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi>)\<rfloor>" by simp    --{* K Schema *}
 lemma NEC: "\<lfloor>\<phi>\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>\<box>\<phi>\<rfloor>" by simp    --{* Necessitation *}

 text {* Instances of the Barcan and converse Barcan Formulas are satisfied for standard (possibilist) quantifiers *}
 lemma "\<lfloor>(\<^bold>\<forall>x.\<^bold>\<box>(\<phi> x)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x.(\<phi> x))\<rfloor>" by simp
 lemma "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>x.(\<phi> x)) \<^bold>\<rightarrow> (\<^bold>\<forall>x.\<^bold>\<box>(\<phi> x))\<rfloor>" by simp
    
 text {* ... but not for actualist quantifiers *}
 lemma "\<lfloor>(\<^bold>\<forall>\<^sup>Ex.\<^bold>\<box>(\<phi> x)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ex.(\<phi> x))\<rfloor>" nitpick oops (** countersatisfiable*)
 lemma "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>\<^sup>Ex.(\<phi> x)) \<^bold>\<rightarrow> (\<^bold>\<forall>\<^sup>Ex.\<^bold>\<box>(\<phi> x))\<rfloor>" nitpick oops (** countersatisfiable*)
 
 text {* Well known relations between meta-logical notions *}
 lemma  "\<lfloor>\<phi>\<rfloor> \<longleftrightarrow> \<not>\<lfloor>\<phi>\<rfloor>\<^sup>c\<^sup>s\<^sup>a\<^sup>t" by simp
 lemma  "\<lfloor>\<phi>\<rfloor>\<^sup>s\<^sup>a\<^sup>t \<longleftrightarrow> \<not>\<lfloor>\<phi>\<rfloor>\<^sup>i\<^sup>n\<^sup>v " by simp
 
 text {* Contingent truth does not allow for necessitation *}
 lemma "\<lfloor>\<^bold>\<diamond>\<phi>\<rfloor>  \<longrightarrow> \<lfloor>\<^bold>\<box>\<phi>\<rfloor>" nitpick oops            (** countersatisfiable*)
 lemma "\<lfloor>\<^bold>\<box>\<phi>\<rfloor>\<^sup>s\<^sup>a\<^sup>t \<longrightarrow> \<lfloor>\<^bold>\<box>\<phi>\<rfloor>" nitpick oops           (** countersatisfiable*)

 text {* Modal Collapse is countersatisfiable *}
 lemma "\<lfloor>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<rfloor>" nitpick oops                  (** countersatisfiable*)

section {* Useful Definitions for Axiomatization of Further Logics *}

 text {* The best known logics \emph{K4, K5, KB, K45, KB5, D, D4, D5, D45, ...} are obtained through
 axiomatization of combinations of the following: *}

  abbreviation M 
    where "M \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi>"
  abbreviation B 
    where "B \<equiv> \<^bold>\<forall>\<phi>. \<phi> \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<diamond>\<phi>"
  abbreviation D 
    where "D \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>"
  abbreviation IV 
    where "IV \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<box>\<phi> \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<box>\<phi>"
  abbreviation V 
    where "V \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>"
  
  text {* Because the embedding is of a semantic nature, it is more efficient to instead make use of 
  the well-known \emph{Sahlqvist correspondence}, which links axioms to constraints on a model's accessibility
  relation: axioms $M, B, D, IV, V$ impose reflexivity, symmetry, seriality, transitivity and euclideanness respectively. *}

  lemma "reflexive aRel  \<Longrightarrow>  \<lfloor>M\<rfloor>" by blast (** aka T *)
  lemma "symmetric aRel \<Longrightarrow> \<lfloor>B\<rfloor>" by blast
  lemma "serial aRel  \<Longrightarrow> \<lfloor>D\<rfloor>" by blast         
  lemma "preorder aRel \<Longrightarrow>  \<lfloor>M\<rfloor> \<and> \<lfloor>IV\<rfloor>" by blast (** S4 - reflexive + transitive*)
  lemma "equivalence aRel  \<Longrightarrow>  \<lfloor>M\<rfloor> \<and> \<lfloor>V\<rfloor>" by blast (** S5 - preorder + symmetric *)
  lemma "reflexive aRel \<and> euclidean aRel  \<Longrightarrow>  \<lfloor>M\<rfloor> \<and> \<lfloor>V\<rfloor>" by blast (** S5 *)

  text {* Using these definitions, we can derive axioms for the most common modal logics. Thereby we 
  are free to use either the semantic constraints or the related Sahlqvist axioms. Here we provide 
  both versions. We recommend to use the semantic constraints for improved performance. *}
    
end