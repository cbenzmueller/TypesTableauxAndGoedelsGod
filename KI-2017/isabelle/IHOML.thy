(*<*)
theory IHOML
imports Relations
begin  
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 3, atoms e = a b c d]
(*>*)
  
(*
\begin{abstract}
 A shallow semantic embedding of an intensional higher-order modal logic (IHOML) in Isabelle/HOL is presented.
 IHOML draws on Montague/Gallin intensional logics and has been introduced by Melvin Fitting in his textbook
 \emph{Types, Tableaus and G\"odel's God} in order to discuss his emendation of G\"odel's ontological argument for the existence of God.
 Utilizing IHOML, the most interesting parts of Fitting's textbook are formalized, automated and verified
 in the Isabelle/HOL proof assistant. A particular focus thereby is on three variants of the ontological argument
 which avoid the modal collapse, which is a strongly criticized side-effect in G\"odel's resp. Scott's original work.
\\ \\
  \textbf{Keywords:} Automated Theorem Proving. Computational Metaphysics. 
	Higher-Order Logic. Intensional Logic. Isabelle.
	Modal Logic. Ontological Argument. Semantic Embedding
\end{abstract}
*)
  
section \<open>Introduction\<close>
  
(**The first part of this paper introduces a shallow semantic embedding of
an intensional higher-order modal logic (IHOML) in classical higher-order logic (Isabelle/HOL\footnote{In this paper 
we work with the Isabelle/HOL proof assistant  @{cite "Nipkow-Paulson-Wenzel:2002"}, which explains the chosen abbreviation. 
Generally, however, the work presented here can be mapped to any other 
system implementing Church's simple type theory  @{cite "Church40"}.}).
IHOML, as introduced by Fitting @{cite "Fitting"}, is a modification of the
intensional logic originally developed by Montague and later expanded by Gallin @{cite "Gallin75"} by building upon Church's
type theory and Kripke's possible-world semantics. Our approach builds on previous work on the semantic embedding of
multimodal logics with quantification @{cite "J23"}, which we expand here to allow for actualist quantification,
intensional terms and their related operations.
From an AI perspective we contribute a highly flexible framework for automated reasoning in intensional and modal logic.
IHOML, which has not been automated before, has several applications, e.g. towards the deep semantic analysis
of natural language rational arguments as envisioned in the new DFG Schwerpunktprogramm RATIO (SPP 1999).*)
  
(**In the second part, we present an exemplary, non-trivial application of this reasoning infrastructure:
A study on \emph{computational metaphysics}\footnote{This term was originally coined by Fitelson and Zalta in @{cite "FitelsonZ07"} and describes
an emerging, interdisciplinary field aiming at the rigorous formalization and deep logical assessment
of philosophical arguments in an automated reasoning environment.},
the computer-formalization and critical assessment of G\"odel's @{cite "GoedelNotes"} (resp. Dana Scott's @{cite "ScottNotes"})
modern variant of the ontological argument and two of its proposed emendations as discussed in @{cite "Fitting"}.
G\"odel's ontological argument is amongst the most discussed formal proofs in modern literature.
Several authors (e.g. @{cite "anderson90,AndersonGettings,bjordal99,Hajek2002,Fitting"}) 
have proposed emendations with the aim of retaining its essential result 
(the necessary existence of God) while at the same time avoiding the \emph{modal collapse} (whatever is the case is so necessarily)
@{cite "Sobel,sobel2004logic"}. The modal collapse is an undesirable side-effect of the axioms postulated by G\"odel (resp. Scott). 
It essentially states that there are no contingent truths and everything is determined.*)
  
(**Related work\footnote{More loosely related work studied  Anselm's older, non-modal version of the ontological argument directly in 
Prover9 @{cite "oppenheimera11"} and PVS @{cite "rushby13"}.} has formalized several of these variants on the computer and verified or falsified them. For example,
G\"odel's axiom's system has been shown inconsistent @{cite "C55,C60"},
while Scott's version has been verified @{cite "ECAI"}. Further experiments, contributing amongst others
to the clarification of a related debate regarding the redundancy of some axioms in Anderson's emendation,
are presented and discussed in @{cite "J32"}.
The enabling technique in these case studies has been shallow semantic embeddings of \emph{extensional}
higher-order modal logics in classical higher-order logic (see @{cite "J23,R59"} and the references therein).\footnote{In contrast to deep semantic embeddings, 
where the embedded logic is presented as an abstract datatype, our shallow semantic embeddings avoid inductive 
definitions and maximize the reuse of logical operations from the meta-level. In particular, tedious new binding mechanisms are avoided 
in our approach.}*)

(**In contrast to the related work, Fitting's variant is based on \emph{intensional} higher-order modal logic.
Our experiments confirm that Fitting's argument, as presented in his textbook @{cite "Fitting"},
is valid and that it avoids the modal collapse as intended.
Due to lack of space, we refer the reader to our (computer-verified) paper @{cite "J35"} for further results.
That paper has been written directly in the Isabelle/HOL proof assistant and requires some familiarity
with this system and with Fitting's textbook.*)
  
(**The work presented here originates from the \emph{Computational Metaphysics} lecture course held at the FU Berlin
in Summer 2016 @{cite "C58"}.*)

section \<open>Embedding of Intensional Higher-Order Modal Logic\<close>

subsection \<open>Type Declarations\<close>  
(**Since IHOML and Isabelle/HOL are both typed languages, we introduce a type-mapping between them.
We follow as closely as possible the syntax given by Fitting (@{cite "Fitting"} p. 86), according to which, 
for any extensional type @{text "\<tau>"}, @{text "\<up>\<tau>"} becomes its corresponding intensional type. For instance,
a set of (red) objects has the extensional type @{text "\<langle>e\<rangle>"}, whereas the concept `red' has intensional type @{text "\<up>\<langle>e\<rangle>"}.*)

  typedecl e                    (**type for entities*)             
  typedecl w                    (**type for possible worlds*)
  type_synonym wo = "(w\<Rightarrow>bool)" (**type for world-dependent formulas*)
    
(**Aliases for some common complex types (predicates and relations).*)
  type_synonym ie="(w\<Rightarrow>e)" ("\<up>e") (**individual concepts (map worlds to objects)*)
  type_synonym se="(e\<Rightarrow>bool)" ("\<langle>e\<rangle>") (**(extensional) sets*)
  type_synonym ise="(e\<Rightarrow>wo)" ("\<up>\<langle>e\<rangle>") (**(intensional predicative) concepts*) 
  type_synonym sise="(\<up>\<langle>e\<rangle>\<Rightarrow>bool)" ("\<langle>\<up>\<langle>e\<rangle>\<rangle>") (**sets of concepts*) 
  type_synonym isise="(\<up>\<langle>e\<rangle>\<Rightarrow>wo)" ("\<up>\<langle>\<up>\<langle>e\<rangle>\<rangle>") (**2-order concepts*)
  type_synonym see="(e\<Rightarrow>e\<Rightarrow>bool)" ("\<langle>e,e\<rangle>") (**(extensional) relations*)
  type_synonym isee="(e\<Rightarrow>e\<Rightarrow>wo)" ("\<up>\<langle>e,e\<rangle>") (**(intensional) relational concepts*)
(*<*)
  type_synonym sie=     "(\<up>e\<Rightarrow>bool)" ("\<langle>\<up>e\<rangle>")
  type_synonym isie=    "(\<up>e\<Rightarrow>wo)" ("\<up>\<langle>\<up>e\<rangle>")
  type_synonym sisise=  "(\<up>\<langle>\<up>\<langle>e\<rangle>\<rangle>\<Rightarrow>bool)" ("\<langle>\<up>\<langle>\<up>\<langle>e\<rangle>\<rangle>\<rangle>")
  type_synonym isisise= "(\<up>\<langle>\<up>\<langle>e\<rangle>\<rangle>\<Rightarrow>wo)"  ("\<up>\<langle>\<up>\<langle>\<up>\<langle>e\<rangle>\<rangle>\<rangle>")
  type_synonym sse =    "\<langle>e\<rangle>\<Rightarrow>bool"         ("\<langle>\<langle>e\<rangle>\<rangle>")
  type_synonym isse =   "\<langle>e\<rangle>\<Rightarrow>wo"          ("\<up>\<langle>\<langle>e\<rangle>\<rangle>")
  type_synonym isisee="(\<up>\<langle>e\<rangle>\<Rightarrow>e\<Rightarrow>wo)" ("\<up>\<langle>\<up>\<langle>e\<rangle>,e\<rangle>") (**2-order relational concepts*)
  type_synonym sieie="(\<up>e\<Rightarrow>\<up>e\<Rightarrow>bool)"       ("\<langle>\<up>e,\<up>e\<rangle>")
  type_synonym isieie =     "(\<up>e\<Rightarrow>\<up>e\<Rightarrow>wo)"        ("\<up>\<langle>\<up>e,\<up>e\<rangle>")
  type_synonym ssese =      "(\<langle>e\<rangle>\<Rightarrow>\<langle>e\<rangle>\<Rightarrow>bool)"     ("\<langle>\<langle>e\<rangle>,\<langle>e\<rangle>\<rangle>")
  type_synonym issese =     "(\<langle>e\<rangle>\<Rightarrow>\<langle>e\<rangle>\<Rightarrow>wo)"      ("\<up>\<langle>\<langle>e\<rangle>,\<langle>e\<rangle>\<rangle>")
  type_synonym ssee =       "(\<langle>e\<rangle>\<Rightarrow>e\<Rightarrow>bool)"       ("\<langle>\<langle>e\<rangle>,e\<rangle>")
  type_synonym issee =      "(\<langle>e\<rangle>\<Rightarrow>e\<Rightarrow>wo)"        ("\<up>\<langle>\<langle>e\<rangle>,e\<rangle>")
  type_synonym isiseise =   "(\<up>\<langle>e\<rangle>\<Rightarrow>\<up>\<langle>e\<rangle>\<Rightarrow>wo)"    ("\<up>\<langle>\<up>\<langle>e\<rangle>,\<up>\<langle>e\<rangle>\<rangle>")
  type_synonym isiseisise=  "(\<up>\<langle>e\<rangle>\<Rightarrow>\<up>\<langle>\<up>\<langle>e\<rangle>\<rangle>\<Rightarrow>wo)" ("\<up>\<langle>\<up>\<langle>e\<rangle>,\<up>\<langle>\<up>\<langle>e\<rangle>\<rangle>\<rangle>")
(*>*) 
subsection \<open>Logical Constants as Truth-Sets\<close>    
(**We embed modal operators as sets of worlds satisfying a corresponding formula.*)
  
  abbreviation mand::"wo\<Rightarrow>wo\<Rightarrow>wo" (infix"\<^bold>\<and>"(*<*)51(*>*)) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<and>(\<psi> w)"
  abbreviation mor::"wo\<Rightarrow>wo\<Rightarrow>wo" (infix"\<^bold>\<or>"(*<*)50(*>*)) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<or>(\<psi> w)"
  abbreviation mimp::"wo\<Rightarrow>wo\<Rightarrow>wo" (infix"\<^bold>\<rightarrow>"(*<*)49(*>*)) where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<longrightarrow>(\<psi> w)"
  abbreviation mequ::"wo\<Rightarrow>wo\<Rightarrow>wo" (infix"\<^bold>\<leftrightarrow>"(*<*)48(*>*)) where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<longleftrightarrow>(\<psi> w)"
  abbreviation mnot::"wo\<Rightarrow>wo" ("\<^bold>\<not>_"(*<*)[52]53(*>*)) where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>(\<phi> w)"
  abbreviation mnegpred::"\<up>\<langle>e\<rangle>\<Rightarrow>\<up>\<langle>e\<rangle>" ("\<^bold>\<rightharpoondown>_"(*<*)[52]53(*>*)) where "\<^bold>\<rightharpoondown>\<Phi> \<equiv> \<lambda>x.\<lambda>w. \<not>(\<Phi> x w)"
(*<*)
  abbreviation xor:: "bool\<Rightarrow>bool\<Rightarrow>bool" (infix"\<oplus>"50)
    where "\<phi>\<oplus>\<psi> \<equiv>  (\<phi>\<or>\<psi>) \<and> \<not>(\<phi>\<and>\<psi>)" 
  abbreviation mxor   :: "wo\<Rightarrow>wo\<Rightarrow>wo" (infix"\<^bold>\<oplus>"50)
    where "\<phi>\<^bold>\<oplus>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<oplus>(\<psi> w)"
  abbreviation negpred :: "\<langle>e\<rangle>\<Rightarrow>\<langle>e\<rangle>" ("\<rightharpoondown>_"[52]53) 
    where "\<rightharpoondown>\<Phi> \<equiv> \<lambda>x. \<not>(\<Phi> x)"  
(*>*)      
(**\emph{Possibilist} quantifiers are embedded as follows.\footnote{Possibilist and actualist quantification
 can be seen as the semantic counterparts of the concepts of possibilism and actualism in the metaphysics of modality.
They relate to natural-language expressions such as `there is', `exists', `is actual', etc.}*)    
  abbreviation mforall::"('t\<Rightarrow>wo)\<Rightarrow>wo" ("\<^bold>\<forall>") where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w.\<forall>x. (\<Phi> x w)"
  abbreviation mexists::"('t\<Rightarrow>wo)\<Rightarrow>wo" ("\<^bold>\<exists>") where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x. (\<Phi> x w)"    
(*<*)
  abbreviation mforallB  :: "('t\<Rightarrow>wo)\<Rightarrow>wo" (binder"\<^bold>\<forall>"[8]9) (*binder notation*)
    where "\<^bold>\<forall>x. (\<phi> x) \<equiv> \<^bold>\<forall>\<phi>"  
  abbreviation mexistsB  :: "('t\<Rightarrow>wo)\<Rightarrow>wo" (binder"\<^bold>\<exists>"[8]9)
    where "\<^bold>\<exists>x. (\<phi> x) \<equiv> \<^bold>\<exists>\<phi>" 
(*>*)      
(**The \emph{actualizedAt} predicate is used to additionally embed \emph{actualist} quantifiers by restricting the domain of quantification
at every possible world. This standard technique has been referred to as \emph{existence relativization} (@{cite "fitting98"}, p. 106),
highlighting the fact that this predicate can be seen as a kind of meta-logical `existence predicate' telling us
which individuals \emph{actually} exist at a given world. This meta-logical concept does not appear in our object language.*)
  consts Actualized::"\<up>\<langle>e\<rangle>" (infix "actualizedAt"(*<*)70(*>*))
  abbreviation mforallAct::"\<up>\<langle>\<up>\<langle>e\<rangle>\<rangle>" ("\<^bold>\<forall>\<^sup>A") (**actualist variants use superscript*)
    where "\<^bold>\<forall>\<^sup>A\<Phi> \<equiv> \<lambda>w.\<forall>x. (x actualizedAt w)\<longrightarrow>(\<Phi> x w)"
  abbreviation mexistsAct::"\<up>\<langle>\<up>\<langle>e\<rangle>\<rangle>" ("\<^bold>\<exists>\<^sup>A")
    where "\<^bold>\<exists>\<^sup>A\<Phi> \<equiv> \<lambda>w.\<exists>x. (x actualizedAt w) \<and> (\<Phi> x w)"
(*<*)
  abbreviation mforallActB::"\<up>\<langle>\<up>\<langle>e\<rangle>\<rangle>" (binder"\<^bold>\<forall>\<^sup>A"[8]9) (**binder notation*)
    where "\<^bold>\<forall>\<^sup>Ax. (\<phi> x) \<equiv> \<^bold>\<forall>\<^sup>A\<phi>"     
  abbreviation mexistsActB::"\<up>\<langle>\<up>\<langle>e\<rangle>\<rangle>" (binder"\<^bold>\<exists>\<^sup>A"[8]9)
    where "\<^bold>\<exists>\<^sup>Ax. (\<phi> x) \<equiv> \<^bold>\<exists>\<^sup>A\<phi>"
(*>*)      
(**Frame's accessibility relation and modal operators.*)
  consts aRel::"w\<Rightarrow>w\<Rightarrow>bool" (infix "r"(*<*)70(*>*))
  abbreviation mbox :: "wo\<Rightarrow>wo" ("\<^bold>\<box>_"(*<*)[52]53(*>*)) where "\<^bold>\<box>\<phi> \<equiv> \<lambda>w.\<forall>v. (w r v)\<longrightarrow>(\<phi> v)"
  abbreviation mdia :: "wo\<Rightarrow>wo" ("\<^bold>\<diamond>_"(*<*)[52]53(*>*)) where "\<^bold>\<diamond>\<phi> \<equiv> \<lambda>w.\<exists>v. (w r v)\<and>(\<phi> v)"
  
  abbreviation meq:: "'t\<Rightarrow>'t\<Rightarrow>wo" (infix "\<^bold>\<approx>"(*<*)60(*>*)) (**standard equality (for all types)*)
    where "x \<^bold>\<approx> y \<equiv> \<lambda>w. x = y"
  abbreviation meqC:: "\<up>\<langle>\<up>e,\<up>e\<rangle>" (infix "\<^bold>\<approx>\<^sup>C"(*<*)52(*>*)) (**equality for individual concepts*)
    where "x \<^bold>\<approx>\<^sup>C y \<equiv> \<lambda>w. \<forall>v. (x v) = (y v)"
  abbreviation meqL:: "\<up>\<langle>e,e\<rangle>" (infix "\<^bold>\<approx>\<^sup>L"(*<*)52(*>*)) (**Leibniz equality for individuals*)
    where "x \<^bold>\<approx>\<^sup>L y \<equiv> \<lambda>w. \<forall>\<phi>. (\<phi> x w)\<longrightarrow>(\<phi> y w)"

subsection \<open>\emph{Extension-of} Operator\<close> 
(**According to Fitting's semantics (@{cite "Fitting"}, pp. 92-4), @{text "\<down>"} is an unary operator applying only to 
 intensional terms. A term of the form @{text "\<down>\<alpha>"} designates the extension of the intensional object designated by 
 @{text "\<alpha>"}, at some \emph{given} world. For instance, suppose we take possible worlds as persons,
 we can therefore think of the concept `red' as a function that maps each person to the set of objects that person
 classifies as red (its extension). We can further state that the intensional term \emph{r} of type @{text "\<up>\<langle>e\<rangle>"} designates the concept `red'.
 As can be seen, intensional terms in IHOML designate functions on possible worlds and they always do it \emph{rigidly}. 
 We will sometimes refer to an intensional object explicitly as `rigid', implying that its (rigidly) designated function has
 the same extension in all possible worlds.\footnote{The notion of \emph{rigid designation} was introduced by Kripke in @{cite "kripke1980"},
 where he discusses its many interesting ramifications in logic and the philosophy of language.}*)

(**Terms of the form @{text "\<down>\<alpha>"} are called \emph{relativized} (extensional) terms; they are always derived
from intensional terms and their type is extensional (in the color example @{text "\<down>r"} would be of type @{text "\<langle>e\<rangle>"}).
Relativized terms may vary their denotation from world to world of a model, because the \emph{extension of} an intensional term can change
from world to world, i.e. they are non-rigid.*)

(**In our Isabelle/HOL embedding, we had to follow a slightly different approach; we model @{text "\<down>"}
as a predicate applying to formulas of the form @{text "\<Phi>(\<down>\<alpha>\<^sub>1,\<dots>\<alpha>\<^sub>n)"}.
For instance, the formula @{text "Q(\<down>a\<^sub>1)\<^sup>w"} (evaluated at world \emph{w}) is modeled as @{text "\<downharpoonleft>(Q,a\<^sub>1)\<^sup>w"}, 
or @{text "(Q \<downharpoonleft> a\<^sub>1)\<^sup>w"} using infix notation, which gets further translated into @{text "Q(a\<^sub>1(w))\<^sup>w"}.*)
  
(*Depending on the particular types involved, we have to define @{text "\<down>"} differently to ensure type correctness
(see \emph{a-d} below). Nevertheless, the essence of the \emph{Extension-of} operator remains the same:
a term @{text "\<alpha>"} preceded by @{text "\<down>"} behaves as a non-rigid term, whose denotation at a given possible world corresponds
to the extension of the original intensional term @{text "\<alpha>"} at that world.*)
  
(**(\emph{a}) Predicate @{text \<phi>} takes as argument a relativized term derived from an (intensional) individual of type @{text "\<up>e"}.*)
  abbreviation extIndArg::"\<up>\<langle>e\<rangle>\<Rightarrow>\<up>e\<Rightarrow>wo" (infix "\<downharpoonleft>"(*<*)60(*>*)) where "\<phi> \<downharpoonleft>c \<equiv> \<lambda>w. \<phi> (c w) w"
(**(\emph{b}) A variant of (\emph{a}) for terms derived from predicates (types of form @{text "\<up>\<langle>t\<rangle>"}).*)
  abbreviation extPredArg::"(('t\<Rightarrow>bool)\<Rightarrow>wo)\<Rightarrow>('t\<Rightarrow>wo)\<Rightarrow>wo" (infix "\<down>"(*<*)60(*>*))
    where "\<phi> \<down>P \<equiv> \<lambda>w. \<phi> (\<lambda>x. P x w) w"      
(*<*)    
(**(\emph{c}) A variant of (\emph{b}) with a second argument (the first one being relativized).*)
  abbreviation extPredArg1::"(('t\<Rightarrow>bool)\<Rightarrow>'b\<Rightarrow>wo)\<Rightarrow>('t\<Rightarrow>wo)\<Rightarrow>'b\<Rightarrow>wo" (infix "\<down>\<^sub>1" 60)
    where "\<phi> \<down>\<^sub>1P \<equiv> \<lambda>z. \<lambda>w. \<phi> (\<lambda>x. P x w) z w"
(**In what follows, the `@{text "\<lparr>_\<rparr>"}' parentheses are an operator used to convert extensional objects into `rigid' intensional ones.*)  
  abbreviation trivialConversion::"bool\<Rightarrow>wo" ("\<lparr>_\<rparr>") where "\<lparr>\<phi>\<rparr> \<equiv> (\<lambda>w. \<phi>)"
(**(\emph{d}) A variant of (\emph{b}) where @{text \<phi>} takes `rigid' intensional terms as argument.*)
  abbreviation mextPredArg::"(('t\<Rightarrow>wo)\<Rightarrow>wo)\<Rightarrow>('t\<Rightarrow>wo)\<Rightarrow>wo" (infix "\<^bold>\<down>" 60)
    where "\<phi> \<^bold>\<down>P \<equiv> \<lambda>w. \<phi> (\<lambda>x. \<lparr>P x w\<rparr>) w" (* where "\<phi> \<^bold>\<down>P \<equiv> \<lambda>w. \<phi> (\<lambda>x u. P x w) w"*)
(*>*) 
subsection \<open>Verifying the Embedding\<close>
(**The above definitions introduce modal logic \emph{K} with possibilist and actualist quantifiers,
as evidenced by the following tests.\footnote{We prove theorems in
Isabelle by using the keyword `by' followed by the name of a proof method.
Some methods used here are: \emph{simp} (term rewriting), \emph{blast} (tableaus), \emph{meson} (model elimination),
\emph{metis} (ordered resolution and paramodulation), \emph{auto} (classical reasoning and term rewriting)
and \emph{force} (exhaustive search trying different tools). In our computer-formalization and assessment of Fitting's textbook @{cite "J35"},
we provide further evidence that our embedded logic works as intended by verifying the book's theorems and examples.}*)
  
  abbreviation valid::"wo\<Rightarrow>bool" ("\<lfloor>_\<rfloor>") where "\<lfloor>\<psi>\<rfloor> \<equiv>  \<forall>w.(\<psi> w)" (**modal validity*)
  lemma K: "\<lfloor>(\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<psi>)) \<^bold>\<rightarrow> (\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi>)\<rfloor>" by simp   (**verifying \emph{K} principle*)
  lemma NEC: "\<lfloor>\<phi>\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>\<box>\<phi>\<rfloor>" by simp          (**verifying \emph{necessitation} rule*)
    
(**Local consequence implies global consequence (not the other way round).\footnote{We utilize here
  (counter-)model finder \emph{Nitpick} @{cite "Nitpick"} for the first time.  
  For the conjectured lemma, \emph{Nitpick} finds a countermodel (not shown here), i.e. a model satisfying all 
  the axioms which falsifies the given formula.}*)
  lemma localImpGlobalCons: "\<lfloor>\<phi> \<^bold>\<rightarrow> \<xi>\<rfloor> \<Longrightarrow> \<lfloor>\<phi>\<rfloor> \<longrightarrow> \<lfloor>\<xi>\<rfloor>" by simp
  lemma "\<lfloor>\<phi>\<rfloor> \<longrightarrow> \<lfloor>\<xi>\<rfloor> \<Longrightarrow> \<lfloor>\<phi> \<^bold>\<rightarrow> \<xi>\<rfloor>" nitpick oops (**countersatisfiable*)
  
(**(Converse-)Barcan formulas are satisfied for possibilist, but not for actualist, quantification.*)
  lemma "\<lfloor>(\<^bold>\<forall>x.\<^bold>\<box>(\<phi> x)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x.(\<phi> x))\<rfloor>" by simp
  lemma "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>x.(\<phi> x)) \<^bold>\<rightarrow> (\<^bold>\<forall>x.\<^bold>\<box>(\<phi> x))\<rfloor>" by simp
  lemma "\<lfloor>(\<^bold>\<forall>\<^sup>Ax.\<^bold>\<box>(\<phi> x)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ax.(\<phi> x))\<rfloor>" nitpick oops (**countersatisfiable*)
  lemma "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>\<^sup>Ax.(\<phi> x)) \<^bold>\<rightarrow> (\<^bold>\<forall>\<^sup>Ax.\<^bold>\<box>(\<phi> x))\<rfloor>" nitpick oops (**countersatisfiable*)
       
(**@{text "\<beta>"}-redex is valid for non-relativized (intensional or extensional) terms.*)
  lemma "\<lfloor>(\<lambda>\<alpha>. \<phi> \<alpha>) (\<tau>::\<up>e) \<^bold>\<leftrightarrow> (\<phi>  \<tau>)\<rfloor>" by simp
  lemma "\<lfloor>(\<lambda>\<alpha>. \<phi> \<alpha>) (\<tau>::e) \<^bold>\<leftrightarrow> (\<phi>  \<tau>)\<rfloor>" by simp
  lemma "\<lfloor>(\<lambda>\<alpha>. \<^bold>\<box>\<phi> \<alpha>) (\<tau>::\<up>e) \<^bold>\<leftrightarrow> (\<^bold>\<box>\<phi> \<tau>)\<rfloor>" by simp
  lemma "\<lfloor>(\<lambda>\<alpha>. \<^bold>\<box>\<phi> \<alpha>) (\<tau>::e) \<^bold>\<leftrightarrow> (\<^bold>\<box>\<phi> \<tau>)\<rfloor>" by simp    
(**@{text "\<beta>"}-redex is valid for relativized terms as long as no modal operators occur.*)
  lemma "\<lfloor>(\<lambda>\<alpha>. \<phi> \<alpha>) \<downharpoonleft>(\<tau>::\<up>e) \<^bold>\<leftrightarrow> (\<phi> \<downharpoonleft>\<tau>)\<rfloor>" by simp
  lemma "\<lfloor>(\<lambda>\<alpha>. \<^bold>\<box>\<phi> \<alpha>) \<downharpoonleft>(\<tau>::\<up>e) \<^bold>\<leftrightarrow> (\<^bold>\<box>\<phi> \<downharpoonleft>\<tau>)\<rfloor>" nitpick oops (**countersatisfiable*)

(**Modal collapse is countersatisfiable.*)
  lemma "\<lfloor>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<rfloor>" nitpick oops   (**countersatisfiable*)
    
subsection\<open>Stability, Rigid Designation, \emph{De Dicto} and \emph{De Re}\<close>
    
(**Intensional terms are trivially rigid. This predicate tests whether an intensional
  predicate is `rigid' in the sense of denoting a world-independent function.*)   
  abbreviation rigid::"('t\<Rightarrow>wo)\<Rightarrow>wo" where "rigid \<tau> \<equiv> (\<lambda>\<beta>. \<^bold>\<box>((\<lambda>z. \<beta>\<^bold>\<approx>z) \<^bold>\<down>\<tau>)) \<^bold>\<down>\<tau>"
    
(**Following definitions are called `stability conditions' by Fitting (@{cite "Fitting"}, p. 124).*)
  abbreviation stabilityA::"('t\<Rightarrow>wo)\<Rightarrow>wo" where "stabilityA \<tau> \<equiv> \<^bold>\<forall>\<alpha>. (\<tau> \<alpha>) \<^bold>\<rightarrow> \<^bold>\<box>(\<tau> \<alpha>)"
  abbreviation stabilityB::"('t\<Rightarrow>wo)\<Rightarrow>wo" where "stabilityB \<tau> \<equiv> \<^bold>\<forall>\<alpha>. \<^bold>\<diamond>(\<tau> \<alpha>) \<^bold>\<rightarrow> (\<tau> \<alpha>)"
  
(**We prove them equivalent in \emph{S5} logic (using \emph{Sahlqvist correspondence}).*)  
  lemma "equivalence aRel \<Longrightarrow> \<lfloor>stabilityA (\<tau>::\<up>\<langle>e\<rangle>)\<rfloor> \<longrightarrow> \<lfloor>stabilityB \<tau>\<rfloor>" by blast    
  lemma "equivalence aRel \<Longrightarrow> \<lfloor>stabilityB (\<tau>::\<up>\<langle>e\<rangle>)\<rfloor> \<longrightarrow> \<lfloor>stabilityA \<tau>\<rfloor>" by blast    
      
(**A term is rigid if and only if it satisfies the stability conditions.*)
  lemma "\<lfloor>rigid (\<tau>::\<up>\<langle>e\<rangle>)\<rfloor> \<longleftrightarrow> \<lfloor>(stabilityA \<tau> \<^bold>\<and> stabilityB \<tau>)\<rfloor>" by meson   
  lemma "\<lfloor>rigid (\<tau>::\<up>\<langle>\<up>e\<rangle>)\<rfloor> \<longleftrightarrow> \<lfloor>(stabilityA \<tau> \<^bold>\<and> stabilityB \<tau>)\<rfloor>" by meson   
      
(**\emph{De re} is equivalent to \emph{de dicto} for non-relativized (i.e. rigid) terms.\footnote{The
  \emph{de dicto/de re} distinction is used regularly in the philosophy of language for disambiguation
  of sentences involving intensional contexts.}*)
  lemma "\<lfloor>\<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) (\<tau>::\<langle>e\<rangle>))  \<^bold>\<leftrightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<tau>)\<rfloor>" by simp
  lemma "\<lfloor>\<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) (\<tau>::\<up>\<langle>e\<rangle>)) \<^bold>\<leftrightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<tau>)\<rfloor>" by simp
(**\emph{De re} is not equivalent to \emph{de dicto} for relativized terms.*)    
  lemma "\<lfloor>\<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<^bold>\<down>(\<tau>::\<up>\<langle>e\<rangle>)) \<^bold>\<leftrightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<^bold>\<down>\<tau>)\<rfloor>" 
    nitpick[card e=1, card w=2] oops (**countersatisfiable*)
      
subsection \<open>Useful Definitions for the Axiomatization of Further Logics\<close>

(**The best-known normal logics (\emph{K4, K5, KB, K45, KB5, D, D4, D5, D45, ...}) can be obtained by
 combinations of the following axioms: *)
  abbreviation T  where "T \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi>"
  abbreviation B  where "B \<equiv> \<^bold>\<forall>\<phi>. \<phi> \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<diamond>\<phi>"
  abbreviation D  where "D \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>"
  abbreviation IV where "IV \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<box>\<phi> \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<box>\<phi>"
  abbreviation V  where "V \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>"
  
(**Instead of postulating combinations of the above  axioms we make use of 
  the well-known \emph{Sahlqvist correspondence}, which links axioms to constraints on a model's accessibility
  relation. We show  that  reflexivity, symmetry, seriality, transitivity and euclideanness imply
  axioms $T, B, D, IV, V$ respectively.\footnote{Implication can also be proven in the reverse direction
  (which is not needed for our purposes).
  Using these definitions, we can derive axioms for the most common modal logics (see also @{cite "C47"}). 
  Thereby we are free to use either the semantic constraints or the related \emph{Sahlqvist} axioms. Here we provide 
  both versions. In what follows we use the semantic constraints for improved performance.}
*)
  lemma "reflexive aRel  \<Longrightarrow>  \<lfloor>T\<rfloor>" by blast
  lemma "symmetric aRel \<Longrightarrow> \<lfloor>B\<rfloor>" by blast
  lemma "serial aRel  \<Longrightarrow> \<lfloor>D\<rfloor>" by blast         
  lemma "transitive aRel  \<Longrightarrow> \<lfloor>IV\<rfloor>" by blast   
  lemma "euclidean aRel \<Longrightarrow> \<lfloor>V\<rfloor>" by blast         
  lemma "preorder aRel \<Longrightarrow> \<lfloor>T\<rfloor> \<and> \<lfloor>IV\<rfloor>" by blast (**S4: reflexive + transitive*)
  lemma "equivalence aRel \<Longrightarrow> \<lfloor>T\<rfloor> \<and> \<lfloor>V\<rfloor>" by blast (**S5: preorder + symmetric*)
(*<*)  
subsection \<open>Textbook Examples\<close>
    
  (**Example 7.13, p. 96:*)
  lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X)  (P::\<up>\<langle>e\<rangle>) \<^bold>\<rightarrow> \<^bold>\<diamond>((\<lambda>X. \<^bold>\<exists>X)  P)\<rfloor>"  by simp    
  lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X) \<^bold>\<down>(P::\<up>\<langle>e\<rangle>) \<^bold>\<rightarrow> \<^bold>\<diamond>((\<lambda>X. \<^bold>\<exists>X) \<^bold>\<down>P)\<rfloor>"
    nitpick[card e=1, card w=2] oops (**nitpick finds same counterexample as book*)
      
  (**Example 7.14, p. 98:*)
  lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X) \<^bold>\<down>(P::\<up>\<langle>e\<rangle>) \<^bold>\<rightarrow> (\<lambda>X. \<^bold>\<exists>X) \<^bold>\<down>P\<rfloor>" by simp
  lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X)  (P::\<up>\<langle>e\<rangle>) \<^bold>\<rightarrow> (\<lambda>X. \<^bold>\<exists>X)  P\<rfloor>" 
    nitpick[card e=1, card w=2] oops (**countersatisfiable *)
      
  (**Example 7.15, p. 99:*)
  lemma "\<lfloor>\<^bold>\<box>(P (c::\<up>e)) \<^bold>\<rightarrow> (\<^bold>\<exists>x::\<up>e. \<^bold>\<box>(P x))\<rfloor>" by auto 
  
  (**Example 7.16, p. 100:*)
  lemma "\<lfloor>\<^bold>\<box>(P \<downharpoonleft>(c::\<up>e)) \<^bold>\<rightarrow> (\<^bold>\<exists>x::e. \<^bold>\<box>(P x))\<rfloor>" 
    nitpick[card e=2, card w=2] oops (**counterexample with two worlds found *)
      
  (**Example 7.17, p. 101:*)
  lemma "\<lfloor>\<^bold>\<forall>Z::\<up>e. (\<lambda>x::e.  \<^bold>\<box>((\<lambda>y::e.  x \<^bold>\<approx> y) \<downharpoonleft>Z)) \<downharpoonleft>Z\<rfloor>" 
    nitpick[card e=2, card w=2] oops (**countersatisfiable *)
  lemma "\<lfloor>\<^bold>\<forall>z::e.  (\<lambda>x::e.  \<^bold>\<box>((\<lambda>y::e.  x \<^bold>\<approx> y)  z)) z\<rfloor>" by simp
  lemma "\<lfloor>\<^bold>\<forall>Z::\<up>e. (\<lambda>X::\<up>e. \<^bold>\<box>((\<lambda>Y::\<up>e. X \<^bold>\<approx> Y)  Z)) Z\<rfloor>" by simp
  
  (**Example 9.1, p.116 (using standard-, Leibniz- and concept-equality)*) (* statesman-like president-material*)
  lemma "\<lfloor>((\<lambda>X. \<^bold>\<box>(X \<downharpoonleft>(p::\<up>e))) \<^bold>\<down>(\<lambda>x. \<^bold>\<diamond>(\<lambda>z. z \<^bold>\<approx> x) \<downharpoonleft>p))\<rfloor>" by auto (* using standard equality *)
  lemma "\<lfloor>((\<lambda>X. \<^bold>\<box>(X \<downharpoonleft>(p::\<up>e))) \<^bold>\<down>(\<lambda>x. \<^bold>\<diamond>(\<lambda>z. z \<^bold>\<approx>\<^sup>L x) \<downharpoonleft>p))\<rfloor>" by auto (* using Leibniz equality *)
  lemma "\<lfloor>((\<lambda>X. \<^bold>\<box>(X  (p::\<up>e))) \<^bold>\<down>(\<lambda>x. \<^bold>\<diamond>(\<lambda>z. z \<^bold>\<approx>\<^sup>C x) p))\<rfloor>" by simp (* using equality as defined for individual concepts *)     
end
(*>*)      