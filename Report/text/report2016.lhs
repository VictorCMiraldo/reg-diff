\documentclass{article}
\usepackage[english]{babel}
\usepackage[a4paper]{geometry}
\usepackage{amsfonts}
\usepackage{amsmath}
\usepackage[all]{xypic}
\usepackage{xcolor}
\usepackage{enumerate}
\usepackage{mathtools}
\usepackage{stmaryrd}
\usepackage{bbm}
\usepackage{tcolorbox}
\usepackage{catchfilebetweentags}
\usepackage{code/excerpts/agda}

%% Margin specs

\geometry{rmargin=2.4in%
         ,lmargin=0.6in%
         ,tmargin=1in%
         ,bmargin=1in%
         }

%% My commands

\newcommand{\warnme}[1]{%
{\color{red} \textbf{$[$} #1 \textbf{$]$}}}

\newcommand{\pe}[1]{%
{\color{blue} \textbf{$[$} #1 \textbf{$]$}}}

\newcommand{\victor}[1]{%
{\color{green!40!black} \textbf{$[$} #1 \textbf{$]$}}}

\newtcolorbox{withsalt}%
             {colback=blue!5!white%
             ,colframe=blue!75!black%
             ,fonttitle=\bfseries%
             ,title={Needs discussion:}}

\newtcolorbox{TODO}%
             {colback=green!5!white%
             ,colframe=green!75!black%
             ,fonttitle=\bfseries%
             ,title={TODO}}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Agda related stuff
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% empty env, maybe later we can add some style to it.
\newenvironment{agdacode}[1][-2em]{%
\vspace{.5em}
\hspace{#1}
\begin{minipage}[t]{.8\textwidth}
}{%
\end{minipage}
\vspace{.5em}
}

\newcommand{\AgdaRaw}[2]{%
\ExecuteMetaData[code/excerpts/#1.tex]{#2}
}

\newcommand{\AgdaDots}{%
\hskip 3.5em \F{$\vdots$}
}

% Default code, no additional formatting.
\newcommand{\Agda}[2]{%
\begin{agdacode}
\AgdaRaw{#1}{#2}
\end{agdacode}
}

% Allows us to specify how much \hskip we want through #3.
\newcommand{\AgdaI}[3]{%
\begin{agdacode}[#3]
\AgdaRaw{#1}{#2}
\end{agdacode}
}

%% Agda shortcuts
\newcommand{\D}[1]{\AgdaDatatype{#1}}
\newcommand{\F}[1]{\AgdaFunction{#1}}
\newcommand{\K}[1]{\AgdaKeyword{#1}}
\newcommand{\N}[1]{\AgdaSymbol{#1}}
\newcommand{\RF}[1]{\AgdaField{#1}}
\newcommand{\IC}[1]{\AgdaInductiveConstructor{#1}}
\newcommand{\ICArgs}[2]{\AgdaInductiveConstructor{#1}$\; #2 $}
\newcommand{\DArgs}[2]{\D{#1}$\; #2 $}

\newcommand{\textrho}{$\rho$}
\newcommand{\textLambda}{$\Lambda$}
\newcommand{\textpi}{$\pi$}
\newcommand{\textmu}{$\mu$}
\newcommand{\textsigma}{$\sigma$}
\newcommand{\textSigma}{$\Sigma$}
\newcommand{\texteta}{$\eta$}
\newcommand{\textDelta}{$\Delta$}
\renewcommand{\textbeta}{$\beta$}
\newcommand{\textalpha}{$\alpha$}
\newcommand{\textPi}{$\Pi$}

% And some others that actually require the unicode declaration
\DeclareUnicodeCharacter {10627}{\{\hspace {-.2em}[}
\DeclareUnicodeCharacter {10628}{]\hspace {-.2em}\}}
\DeclareUnicodeCharacter {8759}{::}
\DeclareUnicodeCharacter {8718}{$\square$}
\DeclareUnicodeCharacter {8799}{$\stackrel{\tiny ? \vspace{-1mm}}{=}$}
\DeclareUnicodeCharacter {8339}{$_x$}
\DeclareUnicodeCharacter {8336}{$_a$}
\DeclareUnicodeCharacter {7523}{$_r$}
\DeclareUnicodeCharacter {7506}{$^\circ$}
\DeclareUnicodeCharacter {8348}{$_t$}
\DeclareUnicodeCharacter {7522}{$_i$}
\DeclareUnicodeCharacter {119924}{$\mathcal{M}$}
\DeclareUnicodeCharacter {8346}{$_p$}
\DeclareUnicodeCharacter {8345}{$_n$}
\DeclareUnicodeCharacter {7524}{$_u$}
\DeclareUnicodeCharacter {8347}{$_s$}
\DeclareUnicodeCharacter {120028}{$\mathcal{M}$}

%%%%%%%%%%%%%%%%%%%%%%%%%%%

% lhs2TeX specifics

%include lhs2TeX.fmt 

\title{Diffing Mutually Recursive Types \\ \small{%
A code tour}}
\author{Victor Cacciari Miraldo \\ \small{%
University of Utrecht}}

\begin{document}
  \maketitle

\section{Our Universe}
%format SOP  = "\F{$\sigma\pi$}"
%format Atom = "\F{Atom}"
%format alpha = "\F{$\alpha$}" 
%format contr = "\F{contr}"

  The universe we are using is a \emph{Sums-of-Products} over
type variables and constant types. 

\Agda{RegDiff/Generic/Regular}{atom-def}

  Constructor \IC{I} refers to the $n$-th type variable whereas \IC{K} refers
to a constant type. Value \textit{ks\#} is passed as a module parameter. We denote
products by $\pi$ and sums by $\sigma$, but they are just lists.

\Agda{RegDiff/Generic/Regular}{prod-def}

\Agda{RegDiff/Generic/Regular}{sum-of-prod-def}

Interpreting these codes is very simple. Here, \F{Parms} is a valuation for
the type variables.

\Agda{RegDiff/Generic/Parms}{Parms-def}

\newcommand{\Interp}[2]{\F{$\llbracket$} #1 \F{$\rrbracket$}_{#2}}
\Agda{RegDiff/Generic/Regular}{sop-denotation-def}

  Note that here, $\F{Parms}\;n$ really is isomorphic to $n$ types that serve
as the parameters to the functor $\F{$\llbracket$} F \F{$\rrbracket$}$. When we
introduce a fixpoint combinator, these parameters are used to to tie the recursion
knot, just like a simple fixpoint: $\mu\;F \equiv F\;(\mu F)$. 
In fact, a mutually recursive family can be easily encoded
in this setting. All we need is $n$ types that refer to $n$ type-variables
each!

\Agda{RegDiff/Generic/Multirec}{Fam-def}

\Agda{RegDiff/Generic/Multirec}{Fix-def}

  This universe is enough to model Context-Free grammars, and hence, provides
the basic bare bones for diffing elements of an arbitrary programming language.
In the future, it could be interesting to see what kind of diffing functionality
indexed functors could provide, as these could have scoping rules and other
advanced features built into them. 

\subsection{SoP peculiarities}

One slightly cumbersome problem we have to circumvent is that the codes for 
type variables and constant types are modeled by \F{Atom}s; whereas the
codes for types are modelled by |SOP|. This requires more discipline to organize our code,
since we have to separate, on the type level, functions that handle one or the other.
Nevertheless, we may wish to see \F{Atom}s as a trivial \emph{Sum-of-Product}.

\Agda{RegDiff/Generic/Regular}{into-sop-def}

  Instead of having binary injections into coproducts, like we would
on a \emph{regular-like} universe, we have $n$-ary injections, or, \emph{constructors}.
We encapsulate the idea of constructors of a |SOP| into a type and write a \emph{view}
type that allows us to look at an inhabitant of a sum of products as a \emph{constructor}
and \emph{data}.

  First, we define constructors:

\Agda{RegDiff/Generic/Regular}{Constr-def}

  Now, a constructor of type $C$ expects some arguments to be able to make
an element of type $C$. This is a product, we call it the \F{typeOf} the constructor.

\Agda{RegDiff/Generic/Regular}{typeOf-def}

  Injecting is fairly simple. 

\Agda{RegDiff/Generic/Regular}{injection-def}

  We finish off with a \emph{view} of $\Interp{ty}{A}$ as a constructor and some
data. This greatly simplify the algorithms later on.

\Agda{RegDiff/Generic/Regular}{SOP-view}

\subsection{Agda Details}

  Here we clarify some Agda specific details that are agnostic to
the big picture. This can be safely skipped on a first iteration.

  As we mentioned above, our codes represent functors on $n$
variables. Obviously, to program with them, we need to apply these to
something. The denotation receives a function $\F{Fin}\;n \rightarrow
\F{Set}$, denoted $\F{Parms}\;n$, which can be seen as a valuation for
each type variable.

  In the following sections, we will be dealing with values of
$\Interp{ty}{A}$ for some class of valuations $A$, though.  We need to
have decidable equality for $A\;k$.
\emph{well-behaved parameter}:

\Agda{RegDiff/Generic/Parms}{WBParms-def}

  The following sections discuss functionality that does not depend on
\emph{parameters to codes}. Hence, we will be passing them as Agda module
parameters. We also set up a number of synonyms to already fix the aforementioned
parameter. The first diffing technique we discuss is the trivial
diff. It's module is declared as follows:

\Agda{RegDiff/Diff/Trivial/Base}{Trivial-module-decl}

  We stick to this nomenclature throughout the code. The first line
handles constant types: \textit{ks\#} is how many constant types we
have, $ks$ is the vector of such types and $keqs$ is an indexed vector
with a proof of decidable equality over such types. The second line
handles type parameters: \textit{parms\#} is how many type-variables our
codes will have, $A$ is the valuation we are using. The last parameter is
a family of decidable equality for A.

  Below are the synonyms we use for the rest of the code:

\Agda{RegDiff/Diff/Trivial/Base}{Trivial-defs}

\Agda{RegDiff/Diff/Trivial/Base}{Trivial-aux-defs}

\section{Computing and Representing Patches}
\newcommand{\PARTIAL}{\mathbf{Par}}
%format Maybe    = "\F{Maybe}"
%format just     = "\IC{just}"
%format nothing  = "\IC{nothing}"
%format forall   = "\forall"

%format apply    = "\F{apply}"

%format (REL p)       = "{" p "}^\flat"
%format (INV p)       = "\overline{" p "}"
%format (CONST x)     = "\underline{" x "}"
%format .             = "\bullet"
%format (CONV x)      = "{" x "}^\circ"
%format *             = "\times"
%format (SINGLR x y)  = "\SingletonRel{" x "}{" y "}"
%format (SPLIT (a) (b)) = "\langle {" a "} , {" b "} \rangle"
%format TOP           = "\top"
%format inj1          = "\IC{$\iota_1$}"
%format inj2          = "\IC{$\iota_2$}"
%format injI          = "\IC{inj}_i"
%format matchI        = "\IC{match}_i"
%format injJ          = "\IC{inj}_j"
%format (inj c)       = "\IC{inj}_{" c "}"
%format pi1           = "\IC{$\pi_1$}"
%format pi2           = "\IC{$\pi_2$}"


  Intuitively, a \textit{Patch} is some description of a
transformation. Setting the stage, let $A$ and $B$ be types, $x : A$
and $y : B$ elements of such types.  A \emph{patch} between $x$ and
$y$ must specify a few parts:

\begin{enumerate}[i)]
  \item An |apply : A -> Maybe B| function, 
  \item such that |apply x == just y|.
\end{enumerate}

Well, |apply| is clearly a partial function, and hence, can be seen
as an arrow in the category $\PARTIAL$ of sets and partial functions (that is,
the Kleisli category of |Maybe|!). We will denote the application function of
|p| by |REL p|. 

It is intuitive that if we can apply a patch |p| to and element |a|,
resulting in |just a'|, there should exist a patch |(INV p)| that
\emph{undo} those changes! That is, when |(INV p)| is applied to |a'|
it must result in |just a|.  We can not ask for pointwise
invertibility of |(REL p)|. This is be the same as asking |(REL p)| to
be total\footnote{To prove this, look at |(REL p)| as a functional
relation: $img\;R \subseteq id$. Then require that |(REL (INV p))| be
of the form $R^\circ$. If $R^\circ$ also needs to be function we have
that $R$ needs to be entire. If $R$ is entire and functional, it is a
function.}.

We can, however, get away if we require that |(REL (INV p)) . (REL p)|
be \emph{less than} the identity function, in the sense that if |a|
belongs in the domain of |(REL p)|, then |(REL (INV p)) ( (REL p) a ) == a|, 
where |.| denotes Kleisli composition.

%format PREC = "\preceq"
Take the cannonical partial order on |Maybe A|, which puts |nothing| as the 
lower bound:
\begin{align*}
  |nothing| & |PREC y| \\
  |just x| &  |PREC just y| \text{ iff } |x == y|
\end{align*}

Then require the following diagrams, in $\PARTIAL$, to commute up to |PREC|:

\begin{displaymath}
\xymatrix@@C=4em@@R=4em{
  A \ar[r]^{|(REL p)|} \ar@@{=}[dr]^{\succeq}_{id} & B
   \ar[d]||{|REL (INV p)|} \ar@@{=}[dr]_(.4){\preceq}^{id} & \\
     & A \ar[r]^{|(REL p)|} & B \\
}
\end{displaymath}

We lift |PREC| pointwise to functions, that is define |f PREC g| by
|forall x; f x PREC g x|, then the diagrams above require
|(REL (INV p)) . (REL p) PREC id| iff |(REL p)
. (REL (INV p)) PREC id|. Which is precisely what an Antitone Galois Connection is! 

Hence, we want |(REL p)| and |(REL (INV p))|
to form a (antitone) Galois Connection with respect to |PREC|.



\begin{withsalt}

\pe{Inspired by Tabareau's "Aspect-oriented programming: a language
for 2-categories", I'm toying with (but not proposing for adoption,
this is still very sketchy!)  the following idea: we define a
2-category where 0-cells are types, 1-cells are antitone Galois
connections (pairs of partial functions) (ie. diff and inverse diff)
between types and 2-cells are residuals. There is a terminal object
"unit": it is a 0-cell 1 such that for all type A, there exists a
(trivial) 1-cell $\mathsf{skip} : A \to 1$ and a unique 2-cell
$1_{\mathsf{skip}} : \mathsf{skip} \Rightarrow \mathsf{skip}$. The
specification of "patch" becomes: for every 1-cell $x : 1 \to A$ and
$y : 1 \to B$ there exists a 1-cell $p : A \to B$ and a 2-cell
$\mathsf{apply} : x \Rightarrow y$. Take this with a pinch of salt: it
is more "wishful thinking" than "sound categorical reasoning".}

\victor{I like the sketch, let me know where this goes! By the way,
not sure we need to carry around the pair of partial functions. The inverse
diff is uniquely determined by the diff!}

\pe{re ``inverse diff uniquely determined by the diff'': I don't think
that this is true. You could for example provide an inverse diff that
fails all the time: it would satisfy our spec above. However, given a
diff code, you can always compute \emph{one} specific inverse. (Which,
btw, should have some sort of universal property that we ought to
characterize!)}

\end{withsalt} 

   Now, let us discuss some code and build some intuition for what is
what in the above schema. We will present different parts of the code,
how do they relate to this relational view and give examples here and there!

\subsection{Trivial Diff}
\label{subsec:trivialdiff}
%format Delta = "\F{$\Delta$}"
%format DeltaS = "\F{$\Delta_s$}"
%format DeltaA = "\F{$\Delta_a$}"
%format DeltaP = "\F{$\Delta_p$}"
%format GUARD s f = "{" f "}\hspace{-.1em}\mid_{" s "}"



   The simplest possible way to describe a transformation is to say
what is the source and what is the destination of such
transformation. This can be accomplished by the Diagonal functor, |Delta|, just
fine.

  Now, take an element |(x , y) : Delta ty tv|. The application is intuitive!
We are expecting to transform |x| into |y|. Before formalizing this, we need
two simple partial functions. Let |GUARD S f| be the domain restriction of |f| to |S|:

\[
  |(GUARD S f) a| = \big \{ 
     \begin{array}{ll}
        f\; a   &, \text{if } a \in S \\
        \bot    &, \text{otherwise}
     \end{array}
\]

We write |GUARD x f| instead of |GUARD {x} f| whenever the type of |x|
is clear. Let |CONST y| denote the \emph{constant $y$} (total) function lifted
to $\PARTIAL$. We then define:

\[ |(REL (x , y))| = |GUARD x (CONST y)| \]

\begin{withsalt}
  In the code, we actually define the application of |Delta| as

\begin{align*}
  |REL (x , x)| &= |id| \\
  |REL (x , y)| &= |GUARD x (CONST y)|
\end{align*}

  This is because we want the patch between $x$ and $y$ to be the patch $p$ that
maximizes the domain of |(REL p)| maintaining |(REL p) x == just y|. 

%{
%format pJ = "p_j"
%format pI = "p_i"

  In fact, let $p_0 , \cdots , p_k$ be all the possible patches between $x$ and $y$.
We want to systematically choose the $p_i$ such that: |(REL pJ) PREC (REL pI)| for $j \leq k$.
%}
\end{withsalt}

\subsubsection{Trivial Diff, in Agda}

  We will be using |Delta ty tv| for the three levels of our universe: atoms, products and sums.
We distinguish between the different |Delta|'s with subscripts $_a$ , $_p$ and $_s$ respectively.
They only differ in type. The treatment they receive in the code is exactly the same!
Below is how they are defined:

\Agda{RegDiff/Diff/Trivial/Base}{delta-polymorphic-def}

  Hence, we define $\F{$\Delta_x$} = \F{delta}\;\Interp{\cdot}{\F{x}}$, for $x \in \{ a , p , s \}$.

\subsection{Spines}
\label{subsec:spines}
%format CONS   = "\IC{:\hspace{-.5em}:}"
%format NIL    = "\IC{[]}"

%format Scns = "\IC{Scns}"
%format Scp  = "\IC{Scp}"
%format SX   = "\IC{SX}"

%format s1  = "s_1"
%format s2  = "s_2"
%format sN  = "s_n"
%format sI  = "s_i"
%format ddd = "\cdots"

%format spine-cns = "\F{spine-cns}"
%format spine    = "\F{spine}"
%format S        = "\F{S}"
%format S-map    = "\F{S-map}"


  We can make the trivial diff better by identifying whether or not
$x$ and $y$ agree on something! In fact, we will aggresively look for copying
oportunities. We start by checking if $x$ and $y$ are, in fact, equal. If they are,
we say that the patch that transforms $x$ into $y$ is \emph{copy}. If they are not equal,
they might have the same \emph{constructor}. If they do, we say that the constructor
is copied and we put the data side by side (zip). Otherwise, there is nothing
we can do on this phase and we just return |Delta x y|.

Note that the \emph{spine} forces $x$ and $y$ to be of the same type! 
In practice, we are only interested in diffing elements of the same language.
It does not make sense to diff a C source file against a Haskell source file. 

Nevertheless, we define an |S| structure to capture this longest common prefix
of $x$ and $y$; which, for the \emph{SoP} universe is very easy to state.

\Agda{RegDiff/Diff/Regular/Base}{Spine-def}

Remember that |contr P x = P x x| and |alpha : Atom n -> SOP n|; Here,
$\F{ListI}\;P\;l$ is an indexed list where the elements have type $P\;l_i$,
for every $l_i \in l$. We will treat this type like an ordinary list
for the remainder of this document.

Note that \F{S} makes a functor (actually, a free monad!) on $P$, 
and hence, we can map over it:

\Agda{RegDiff/Diff/Regular/Base}{S-map-def}

Computing a spine is easy, first we check whether or not $x$ and
$y$ are equal. If they are, we are done. If not, we look at $x$ and $y$ as
true sums of products and check if their constructors are equal, if they are,
we zip the data together. If they are not, we zip $x$ and $y$ together and give up.

\Agda{RegDiff/Diff/Regular/Base}{spine-def}

Note that when both arguments to |spine-cns| have the same constructor (they
already have the same type) we can safely zip their arguments! This speeds
up the process, as this is \emph{not} an alignment problem. Besides some
more complicated types, the zip function is as usual:

\Agda{RegDiff/Diff/Regular/Base}{zip-product-def}

The application functions specified by a spine |s = spine x y|, 
denoted |REL s| are defined, in $\PARTIAL$, by:

\begin{align*}
  |REL Scp|           &= \hspace{3.3em} \xymatrix@@C=12.5em{ A & A \ar[l]_{id}} \\
  |REL (SX p)|        &= \hspace{3.3em} \xymatrix@@C=12.5em{ A & A \ar[l]_{|REL p|} } \\
  |REL (Scns i [s1 , ddd , sN])|   
                 &= \xymatrix@@C=13em{ \amalg_k \Pi_j A_{kj} & \amalg_k \Pi_j A_{kj} 
                                    \ar[l]_{|injI . ((REL s1) * ddd * (REL sN)) . matchI|}}
\end{align*}

  where |injI| is the injection, with constructor $i$, into $\amalg_k T_k$. It corresponds to the function \F{injection}; whereas |matchI| is the inverse: pattern matching
on constructor $i$.

  Appendix \ref{appendix:productskleisli} clarifies some aspects about products and coproducts
on $\PARTIAL$. Long story short, we have that |pi1 . (SPLIT f g) PREC f| and |pi2 . (SPLIT f g) PREC g|!
The proof is not very complicated once we know that |Maybe| is a commutative monad. Semantically
speaking, |((REL s1) * ddd * (REL sN))| is only defined on an input $(x_1 , \cdot , x_n)$ iff 
every |(REL sI)| is defined on $x_i$, which meets one intuition.

  Note that, in the |(SX p)| case, we simply ask for the application function
of |p|. The algorithm produces a |S DeltaS|, so we have pairs on the leaves of the
spine. In fact, either we have only one leave or we have $arity\; C_i$ leaves, where
$C_i$ is the common constructor of $x$ and $y$ in |spine x y|.

  For a running example, let's consider a datatype defined by:

\Agda{Report/code/Examples}{Example-2-3-TREE-F}

  We ommit the \IC{fz} for the \F{I} parts, as we only have one type variable.
We also use \F{$\_\oplus\_$} and \F{$\_\otimes\_$} as aliases for \IC{\_:\hspace{-.5em}:\_} with different
precedences. As expected, there are three constructors:

\Agda{Report/code/Examples}{Example-2-3-TREE-F-Constr}
%format Node2 = "\F{2-node`}"
%format Node3 = "\F{3-node`}"
%format Node0 = "\F{nil`}"
%format unit  = "\IC{unit}"

  We can then consider a few spines over $\Interp{\F{2-3-TREE-F}}{\F{Unit}}$ to illustrate the algorithm:
\begin{align*}
  | spine Node0 (Node3 10 unit unit unit) | 
      &= | SX (Node0 , Node3 10 unit unit unit) | \\
  | spine (Node2 10 unit unit) (Node2 15 unit unit) | 
      &= | Scns Node2 [ (10 , 15) , (unit , unit) , (unit , unit) ] | \\
  | spine Node0 Node0 | &= | Scp | \\
\end{align*}

  In the case where the spine is |Scp| or |Scns i| there is nothing left to be done and we have
the best possible diff. Note that on the |Scns i| case we do \emph{not} allow for rearanging of the
parameters of the constructor |i|. 

  In the case where the spine is |SX|, we can do a better job! We can record which constructor changed into 
which and try to reconcile the data from both the best we can. Going one step at a time, let's first
change one constructor into the other.

  It is important to note that if the output of |spine| is a |SX|, then the constructors
are \emph{different}.

\subsection{Constructor Changes}
\label{subsec:changes}

%format CX     = "\IC{CX}"

%format C      = "\F{C}"
%format change = "\F{change}"
%format C-map  = "\F{C-map}"
%format C-mapM = "\F{C-mapM}"
  
  Let's take an example where the spine can not copy anything:

\begin{align*}
  |s| &= | spine (Node2 10 unit unit) (Node3 10 unit unit unit) | \\
      &= | SX (Node2 10 unit unit , Node3 10 unit unit unit) | \\
\end{align*}

  Here, we wish to say that we changed a |Node2| into a |Node3|. But we are then left with a problem
about what to do with the data inside the |Node2| and |Node3|; this is where the notion of
alignment will be in the picture. For now, we abstract it away by the means of a parameter, 
just like we did with the |S|. This time, however, we need something that receives products 
as inputs.

\Agda{RegDiff/Diff/Regular/Base}{C-def}

  Note that |C| also makes up a functor, and hence can be mapped over:

\Agda{RegDiff/Diff/Regular/Base}{C-map-def}

  Computing an inhabitant of |C| is trivial:

\Agda{RegDiff/Diff/Regular/Base}{change-def}

  Now that we can compute change of constructors, we can refine our |s| above.
We can compute |S-map change s| and we will have:

\begin{align*}
  c &= |S-map change s| \\
    &= | SX (CX Node2 Node3 ((10 , unit , unit) , (10 , unit , unit , unit))) |
\end{align*}

  The application induced by |C| is trivial. We just need to pattern match,
change the data of the constructor in whatever way we need, then inject into another type.

\begin{displaymath}
\xymatrix{  V  &  T \ar[l]_{|(REL (CX i j p))|} \ar[d]^{|matchI|}  \\
            \F{typeOf}\;V\;j \ar[u]^{|injJ|} & \F{typeOf}\;T\;i \ar[l]^{|(REL p)|}
         }
\end{displaymath}

Note that up until now, everything was deterministic! This is something we are bound to lose
when talking about alignment.

\subsection{Aligning Everything}
\label{subsec:align}
%format A0     = "\IC{A0}"
%format Ap1    = "\IC{Ap1}"
%format Ap1o   = "\IC{Ap1$^\circ$}"
%format AX     = "\IC{AX}"

%format align      = "\F{align}"
%format align*  = "\F{align$^*$}"
%format Al      = "\F{Al}"
%format Al-mapM = "\F{Al-mapM}"

%format a1 = "a_1"
%format a2 = "a_2"

On the literature for version control system, the \emph{alignment} problem is the problem
of mapping two strings $l_1$ and $l_2$ in $\mathcal{L}$ into $\mathcal{L} \cup \{ - \}$, for $ \{ - \} \nsubseteq \mathcal{L}$ 
such that the resulting strings $l_1'$ and $l_2'$ are of the same length such that
for all $i$, it must not be happen that $l_1'[i] = - = l_2'[i]$. For example,
Take strings $l_1 = "CGTCG"$ and $l_2 = "GATAGT"$, then, the following is an (optimal)
alignment:

\begin{center}
\begin{tabular}{c c c c c c c}
  C & G & - & T & C & G & - \\
  - & G & A & T & A & G & T
\end{tabular}
\end{center}

Let $\mathcal{DNA} = \{A , T , C , G\}$. Finding the table above is the same as
finding a partial map:

\[ f : \mathcal{DNA}^5 \rightarrow \mathcal{DNA}^6 \]

such that $f\; (C,G,T,C,G) = (G,A,T,A,G,T)$. There are many ways of defining such
a map. We would like, however, that our definition have a maximal domain, that is, we
impose the least possible amount of restrictions. In this case, we can actually define $f$ 
with some pattern matching as:

\[
\begin{array}{l l l}  
  f & (C , x , y , C , z) & = (x , A , y , A , z , T) \\
  f & \_ & = \text{undefined}
\end{array}
\] 

And it is easy to verify that, in fact, $f\; (C,G,T,C,G) = (G,A,T,A,G,T)$. Moreover,
this is the \emph{maximal} such $f$ that still (provably) assigns the correct destination
to the correct source.

On our running example, the leaf of |c| has type |DeltaP (typeOf Node2) (typeOf Node3)|, and it's
value is |((10 , unit , unit) , (10 , unit , unit , unit))|. Note that we are now dealing with
products of different arity. This step will let us say how to \emph{align} one with the other!

On our example, as long as we align the 10 with the 10, the rest does not matter. One optimal
alignment could be:

\begin{center}
\begin{tabular}{cccc}
   |10| & $-$ & |unit| & |unit|  \\
   |10| & |unit| & |unit| & |unit|
\end{tabular}
\end{center}

\subsubsection{Back to Agda}

We will look at alignments from the ``finding a map between products'' perspective.
Here is where our design space starts to grow, and so, we should start making
some distinctios:
\begin{itemize}
  \item We want to allow sharing. This means that the there can be more than one variable
        in the defining pattern of our $f$.
  \item We do \emph{not} allow permutations, as the search space would be too big.
        This means that the variables appear in the right-hand side of $f$ in the
        same order as they appear in the left-hand-side.
  \item We do \emph{not} allow contractions nor weakenings. That is, every variable
        on the left-hand-side of $f$ must appear \emph{exactly} once on the right-hand-side.
\end{itemize}

\begin{withsalt}
  As Pierre points out: 
  \begin{quote}
    The positive type/negative type distinction I keep
    referring to and which drives my intuition is used to structure proof
    search in linear logic. There, the product would be called an
    \emph{asynchronous} connective while the sum would be called a
    \emph{synchronous} connective. Quoting ``Focusing and Polarization in
    Intuitionistic Logic'', ``the search for a focused proof can
    capitalize on this classification by applying [..]  all invertible
    rules [related to an asynchronous connective] in any order (without
    the need for backtracking) and by applying a chain of non-invertible
    rules [related to a synchronous connective] that focus on a given
    formula and its positive subformulas.''. So my gut tells me that your
    diff computation is structured in two (repeating) phases: one that
    generates the spine \& change, yielding several \textbf{independant}
    alignment problems which could be solved concurrently.
  \end{quote}
\end{withsalt}
\begin{withsalt}
  Which is, in fact true! The spine \& change is deterministic and
  the alignment problems we have to solve are independent. I believe
  we could exploit some paralallelism. It will be far from trivial though.
\end{withsalt}

The following datatype describe such maps:

\Agda{RegDiff/Diff/Regular/Base}{Al-def}

Note that the indexes of |Al|, although represented as lists are, in fact, products. Well,
turns out that lists and products are not so different after all. Let us represent the $f$ we
devised on the $\mathcal{DNA}$ example using |Al|. Recall $f \;(C , x , y , C , z) = (x , A , y , A , z , T)$.

\[
%format bC = "C"
| f == Ap1 bC (AX Scp (Ap1o A (AX Scp (AX (bC , A) (AX Scp (Ap1o T A0)))))) |
\]

If we rename |Ap1| to \emph{del}; |Ap1o| to \emph{ins} and |AX| to \emph{mod} we see some familiar
structure arising! Aligning products is the same as computing the diff between heterogeneous lists!
In fact, the |align| function is defined as:

\Agda{RegDiff/Diff/Regular/Base}{align-star-def}

We are now doing things in the |List| monad. This is needed because there 
are many possible alignments between two products. For the moment, we 
refrain from choosing and compute all of them.

%format filter = "\F{filter}"
On another note, some of these alignments are simply dumb! We do not want
to have both |Ap1 x (Ap1o y a)| and |AX (x , y) a|. They are the same alignment.
The |filter|s are in charge of pruning out those branches from the search space. 

\begin{withsalt}
  We need a better way to optimize this. Preferably one that we can also use
to optimize the mutually recursive variant.
\end{withsalt}

Sticking with our example, we can align the leaves of our |c| by computing the following
expression, where |C-mapM| is simply the monadic variant of |C-map|.
\begin{align*}
  |a| &= | C-mapM align* c | \\
      &= | SX (CX Node2 Node3 (AX (10 , 10) (AX (unit , unit) ddd))) | \\
      & \hspace{1em} | CONS SX (CX Node2 Node3 (Ap1 10 (AX (unit , 10) ddd))) | \\
      & \hspace{1em} | CONS SX (CX Node2 Node3 (Ap1 10 (Ap1 unit ddd))) | \\
      & \hspace{1em} | CONS SX (CX Node2 Node3 (Ap1o 10 (AX (10 , unit) ddd))) | \\
      & \hspace{1em} | ddd | \\
\end{align*}

Now we have a problem. Which of the patches above should we chose to be \emph{the}
patch? Recall that we mentioned that we wanted to find the alignment with \emph{maximum domain}.
Something interesting happens if we look at patches from their ``application'' relation, but first,
we define the ``application'' relations of |Al|:

\begin{align*}
  | REL (AX a1 a2)| &= \xymatrix@@C=7em{ B \times \Pi D & A \times \Pi C \ar[l]_{|(REL a1) * (REL a2)|}} \\
  | REL (Ap1 x a)|  &= \hspace{2.4em} \xymatrix@@C=7em{ \Pi B & X \times \Pi A \ar[l]_{|pi2 . (GUARD x ! * (REL a))|}} \\
  | REL (Ap1o x a)| &= \xymatrix@@C=7em{ X \times \Pi B & \Pi A \ar[l]_{ |SPLIT (CONST x) (REL a)| }} \\ 
  | REL A0|         &= \hspace{3.1em} \xymatrix@@C=7em{ \mathbbm{1} & \mathbbm{1} \ar[l]_{ \top } }
\end{align*}

\begin{TODO}
  The next section needs to be completely reestructured.
  I'm here!
\end{TODO}

\section{Patches as Relations}
\label{sec:patchesasrelations}

In order to better illustrate this concept, we need a simpler example first. 
Let's consider the following type with no type variables:

\Agda{Report/code/Examples}{Patches-as-Rels-Type}

It clearly has two constructors:

\Agda{Report/code/Examples}{Patches-as-Rels-Type-constr}

Now, let's take two inhabitants of \F{Type1}.

\Agda{Report/code/Examples}{Patches-as-Rels-Type-els}

There are two possible options for $\F{diff}\;x\;y$:

\Agda{Report/code/Examples}{Patches-as-Rels-all-diffs}.

Consider the semantics for |Delta| as described in
the discussion box at Section~\ref{subsec:trivialdiff}, that is, 

\[ |(REL (x , y)) = | \Big \{ \begin{array}{l l}
                                     |id| & \text{if } |x == y| \\
                                     |(CONST y) . (CONV (CONST x))| & \text{otherwise}
                               \end{array}
\]

Then it becomes clear that we want to select patch (P2) instead of (P1). 
In fact, there is a deeper underlying reason for that! Looking at the two 
patches as relations (after some simplifications), we have:

%format Cns1 = "\IC{C$_1$}"
%format Cns2 = "\IC{C$_2$}"
\begin{align*}
  |(REL P1)| & | = (inj Cns1) . (CONV (SPLIT ((CONST 4) . (CONV (CONST 10))) (CONST 10))) . (CONV (inj Cns2)) | \\
  |(REL P2)| & | = (inj Cns1) . (CONV (SPLIT (CONST 4) id)) . (CONV (inj Cns2)) |
\end{align*}

Drawing them in a diagram we have:

\newcommand{\SingletonRel}[2]{lalala}
\newcommand{\typeOf}[2]{\F{typeOf}_{#1}\;#2}
\renewcommand{\Interp}[1]{\F{$\llbracket$} #1 \F{$\rrbracket$}}
\newcommand{\NAT}{\mathbbm{N}}
\newcommand{\UNIT}{\mathbbm{1}}
\begin{displaymath}
\xymatrix@@C=5em{%
  { \typeOf{\F{Type1}}{|Cns2|} \equiv \NAT \times \NAT }
       \ar@@<-.6ex>[d]_{<\underline{4} , id>^\circ} \ar@@<.6ex>[d]^{< \SingletonRel{10}{4} , \underline{10} >^\circ} 
     & \Interp{\F{Type1}} \ar[l]_(0.4){|(CONV (inj Cns2))|}  \ar@@{-->}@@<-.6ex>[d]_{P2^\flat} \ar@@{-->}@@<.6ex>[d]^{P1^\flat} \\
  { \typeOf{\F{Type1}}{|Cns1|} \equiv \NAT } \ar[r]_(0.6){|(inj Cns1)|} 
     & \Interp{\F{Type1}}
}
\end{displaymath}

Here, we have something curious going on... We have that $P1^\flat \subseteq P2^\flat$.
To see this is not very hard. First, composition and converses are monotonous with respect
to $\subseteq$. We are left to check that:

\newcommand{\subrel}{\;\subseteq\;}
\newcommand{\JustBy}[2]{& \hspace{-2em} #1 \{ \text{ #2 } \} \\}
\newcommand{\Just}[1]{\JustBy{\equiv}{#1}}
\newcommand{\Nojust}{& \hspace{-2em} \equiv \\}
\newcommand{\StartProof}[1]{ & \hspace{2em} #1 \\ }
\begin{align*}
          & < \SingletonRel{10}{4} , \underline{10} > \subrel < \underline{4} , id > \\
  \Just{ split universal }
          & \pi_1 \cdot < \SingletonRel{10}{4} , \underline{10} > \subrel \underline{4} 
            \; \wedge \; \pi_2 \cdot < \SingletonRel{10}{4} , \underline{10} > \subrel id
\end{align*}

The first proof obligation is easy to calculate with:

\begin{align*}
   & \pi_1 \cdot < \SingletonRel{10}{4} , \underline{10} > \subrel \underline{4} \\
 \JustBy{\Leftarrow}{ $\pi_1$-cancel ; $\subrel$-trans }
   & \SingletonRel{10}{4} \subrel \underline{4} \\
 \JustBy{\Leftarrow}{ Leibniz }
   & \SingletonRel{10}{4} \cdot \underline{10} \subrel \underline{4} \cdot \underline{10} \\
 \Just{ $\underline{a}^\circ \cdot \underline{a} \equiv \top$ }
   & \underline{4} \cdot \top \subrel \underline{4} \cdot \underline{10} \\
 \Just { $\underline{a} \cdot \underline{b} \equiv \underline{a}$ }
   & \underline{4} \cdot \top \subrel \underline{4} \\
 \Just { $\underline{a} \cdot \top \equiv \underline{a}$ } 
   & \underline{4} \subrel \underline{4} \\
 \Just { $\subrel$-refl }
   & True
\end{align*}

The second is easier to prove once we add variables!

\begin{align*}
   & \pi_2 \cdot < \SingletonRel{10}{4} , \underline{10}> \subrel \; id \\
  \Just{ Add variables }
   & \forall x, y \; . \; x \; (\pi_2 \cdot < \SingletonRel{10}{4} , \underline{10}>) \; y \Rightarrow x = y \\
  \Just{ PF expand composition }
   & \forall x, y \; . \exists z \; . \; x \; (\pi_2) \; z \wedge z \; < \SingletonRel{10}{4} , \underline{10}> \; y \Rightarrow x = y \\
  \Just{ Types force $z = (z_1 , z_2)$ }
   & \forall x, y \; . \exists z_1 , z_2 \;. \; x \; (\pi_2) \; (z_1 , z_2) \wedge (z_1 , z_2) \; < \SingletonRel{10}{4} , \underline{10}> \; y \Rightarrow x = y \\
  \Just{ $\pi_2$ def }
   & \forall x, y \; . \exists z_1 , z_2 \;. \; x = z_2 \wedge (z_1 , z_2) \; < \SingletonRel{10}{4} , \underline{10}> \; y \Rightarrow x = y \\
  \Just{ split def }
   & \forall x, y \; . \exists z_1 , z_2 \;. \; x = z_2 \wedge z_1 \; (\SingletonRel{10}{4}) \; y \wedge z_2 \; (\underline{10}) \; y \Rightarrow x = y \\
  \Just{ points def }
   & \forall x, y \; . \exists z_1 , z_2 \;. \; x = z_2 \wedge z_1 = 4 \wedge y = 10 \wedge z_2 = 10 \Rightarrow x = y \\
  \Just{ substitutions ; weakening }
   & \forall x, y \; . \exists z_2 \;. \; x = 10  \wedge y = 10 \Rightarrow x = y \\
  \Just{ trivial }
   & True 
\end{align*}

Nevertheless, it is clear which patch we should choose! We should
always choose the patch that gives rise to the biggest relation, as
this is applicable to much more elements.

Hence, our \emph{cost} functions will count how many elements of the domain
and range of the ``application'' relation of a patch are \emph{fixed}. Note that
the |S| and |C| parts of the algorithm are completely deterministic, hence they
should \emph{not} contribute to cost:

\Agda{RegDiff/Diff/Regular/Base}{S-cost-def}

\Agda{RegDiff/Diff/Regular/Base}{C-cost}

An |Al|ignment might fix one element on the source, using |Ap1| or one
element on the destination, using |Ap1o|. 

\Agda{RegDiff/Diff/Regular/Base}{Al-cost-def}

Last but not least, a |Delta| will either fix 2 elements: one
in the source that becomes one in the destination; or none, when
we just copy the source.

\Agda{RegDiff/Diff/Trivial/Base}{cost-delta-polymorphic-def}

According to these definitions, the cost of (P1) above is 3, where
the cost of (P2) is 1.

\subsection{Patches for Regular Types}

Now that we have \emph{spines}, \emph{changes} and \emph{alignments}
figured out, we can define a patch as:

%format Patch = "\F{Patch}"
%format List  = "\F{List}"
\Agda{RegDiff/Diff/Regular/Base}{Patch-def}

Computing inhabitants of such type is done with:

\Agda{RegDiff/Diff/Regular/Base}{diff1-star-def}

where \F{Patch$^*$} is defined as |List (Patch DeltaA)|.

\subsection{Conjectures About the \F{cost} function}

  Here we conjecture a few lemmas about the interplay of the
cost function and the ``application'' relation. Let |P, Q| and |R|
be patches.

%format ==>   = "\Rightarrow"
%format cost  = "\F{cost}"
%format <@ = "\subseteq"
%format Ex = "\exists"
\begin{enumerate}[i)]
  \item If |P| has a lower cost than |Q|, then the domain and range of the ``application'' relation
        of |P| contains the ``application'' relation of |Q|.

        \[ | cost P < cost Q ==> (REL Q) <@ (REL P) . TOP . (REL P) | \]

        \begin{withsalt}
          This is not as simple as 
            \[ | cost P < cost Q ==> (REL Q) <@ (REL P) | \]
          Take two |Deltas|, |px = (10 , 50)| and |py = (30 , 30)|.
          Trivially, |cost py = 0| and |cost px = 2|. 
          Now, |(REL px) = (SINGLR 10 50)| and |(REL py) = id|.
          It is not true that |(SINGLR 10 50) <@ id|!

          If we state, however: Let |P , Q| in |diff* x y|; 
               | cost P < cost Q ==> (REL Q) <@ (REL P) |
          Seems more likely. As the above counter example would not
          work anymore. |diff* 10 50 = (10 , 50) CONS NIL|.
               
        \end{withsalt}
        
  \item If |P| and |Q| have equal cost, it means that there is at least
        one place where |P| and |Q| are doing \emph{the same thing}, hence
        there is a patch that copies this \emph{same thing} and costs
        strictly less.
 
        \[ | cost P == cost Q ==> Ex R . cost R < cost P | \]
\end{enumerate}

\section{Mutually Recursive Types}

Now that we have a clear picture of regular types, 
extending this to recursive types is not
very difficult.

First, recall that a mutually recursive family is defined as $n$ codes that
each reference $n$ type variables:

\Agda{RegDiff/Generic/Multirec}{Fam-def}

\Agda{RegDiff/Generic/Multirec}{Fix-def}

Another auxiliary definition we use here is the indexed coproduct,
which let's us \emph{extend} some indexed type.

\Agda{RegDiff/Diff/Multirec/Base}{UUSet-coprod}

Now, we already have the ingredients for detecting and representing common constructors
or full copies, with |S|, constructor changes, with |C| and alignments with |Al|.
We just need to handle type variables to tie the knot. Before we proceed with the nasty
definitions, we still need two last synonyms:

\Agda{RegDiff/Diff/Multirec/Base}{Fami-def}

Here $\F{T}\;k$ represents the $k$-th type of the family, and \F{Fam$_i$} acts a the
the types in the family.  

We start defining a patch for fixed points by allowing normal patches
to perform changes on the first layer.

\Agda{RegDiff/Diff/Multirec/Base}{Patchmu-skel-def}

However, a patch for a fixed point might not only follow the precise order of
operations (\F{S}, then \F{C}, then \F{Al}) that regular types
enjoyed. For instance, imagine we are transforming the following
lists:

\[
  [5 , 8 , 13 , 21] \rightsquigarrow [8 , 13 , 21]
\]

Let lists be seen (as usual) as the initial algebras of $L_A\;X = 1 + A\times X$;
then, both lists are inhabitants of $\mu L_{\mathbbm{N}}$, but, more precisely,
the source is an inhabitant of $L_{\mathbbm{N}} (L_{\mathbbm{N}} (L_{\mathbbm{N}} (L_{\mathbbm{N}}\; \mathbbm{1})))$
whereas the target is an inhabitant of $L_{\mathbbm{N}} (L_{\mathbbm{N}} (L_{\mathbbm{N}}\; \mathbbm{1}))$.

Here, we are already beginning with different types, so a spine (which
is homogeneous) might not be the best start! In fact, the best start
is to say that the first $5$ is deleted, then the spine can kick in
and say that everything else is copied!

Deleting and inserting can be seen as alignments between a type variable and
the type we wish to delete or insert. For instance, deleting |5|, which is actually |5 CONS _|, consists in deleting the |_ CONS _| constructor and aligning
the $\mathbbm{N} \times \IC{I}\;k$ with with a type variable $\IC{I}\;k$.
Insertions are analogous.

\AgdaI{RegDiff/Diff/Multirec/Base}{Patchmu-ins-del-def}{-.7em}

%format UUtoAA = "\F{UU$\rightarrow$}\F{AA}"
%format Patchmu = "\F{Patch$\mu$}"
Note, however, that we use |UUtoAA Patchmu| to populate the leaves of
|Patch| and |Al|. That's because their parameter is of type |Atom -> Atom -> Set|,
but |Patchmu| has type |U -> U -> Set|. Nevertheless, when these leaves are just two
type variables, we want to keep using |Patchmu| to record their differences.
When these leaves are constant types, we give up and set their values with a delta. 

\AgdaI{RegDiff/Diff/Multirec/Base}{Patchmu-fix-set-def}{-.7em}

Associating costs are trivial. We just piggy back on the previous cost definitions.
I am still very puzzled for how this works.

\Agda{RegDiff/Diff/Multirec/Base}{Patchmu-cost}

Nevertheless, the heart of the algorithm is the same as
any patching algorithm out there. Things can be modified, inserted or
deleted:

\Agda{RegDiff/Diff/Multirec/Base}{diff-mu-non-det}

Modifying must happen at the same type only, otherwise we force an
insertion or deletion. If we are, in fact, on the same type, we can get
the patch for that layer and continue diffing atoms.

\Agda{RegDiff/Diff/Multirec/Base}{diffmu-mod}

Atoms are easy to diff. If reach two type variables, we tie the knot and keep patching.
If we reach two constants, we set one into the other. Any other situation is forbiden.

\Agda{RegDiff/Diff/Multirec/Base}{diffmu-atoms}

Insertions and deletions are very simple:

\Agda{RegDiff/Diff/Multirec/Base}{diffmu-ins}

\Agda{RegDiff/Diff/Multirec/Base}{diffmu-del}

We just need to pay attention not to insert or delete some constructor
without arguments; This is done on the auxiliar alignment function:

\Agda{RegDiff/Diff/Multirec/Base}{alignmu-nonempty-def}

Which ignores empty products. If we are not aligning empty products,
we can just piggyback on the previous alignment function we had:

\Agda{RegDiff/Diff/Multirec/Base}{alignmu-def}

Now we just need to choose the patch with the least cost
for the \emph{deterministic} version. 

\Agda{RegDiff/Diff/Multirec/Base}{diffmu-det}

%format diffmustar = "\F{diffmu$^*$}"
%format NAT  = "\F{$\mathbbm{N}$}"
%format inject = "\F{inject}"
%format BOOL  = "\F{Bool}"
%format true = "\IC{true}"
%format K    = "\IC{K}"
%format fz   = "\IC{fz}"
%format fs   = "\IC{fs}"
\begin{withsalt}
  If we define a family of two types, say |K NAT CONS K BOOL CONS NIL|. Now take
  |x = inject fz 10| and |y = inject (fs fz) true|. 

  \vspace{1em}

  Here, |diffmustar x y = NIL|. It is easy to see why. We can't modify because
  we havetwo different types. We can't insert or delete because \emph{both}
  inhabitants were constructed with constructors that have no recursive arguments.

  \vspace{1em}

  In a real scenario, though, this will never happen. Mainly because we are only
  interested in diffing things of the same type. Sure, the types might change 
  during the algorithm, but they start the same; hence at least a modify is always possible.

  \vspace{1em}

  On another note; The aforementioned type family is not really a type family, but a
  single type: $\mathbbm{N} + \mathbbm{B}$.
\end{withsalt}

Obviously, we can also define the ``application'' relation for fixed points, and that
is done in \texttt{RegDiff/Diff/Multirec/Domain}. I believe it is more worthwhile to
look at some example patches and their ``application'' relation instead of the general
case, though. Let's begin with the lists we just discussed:

\Agda{Report/code/Examples}{Example-list-2}

Here, \F{LIST-F} is defined as $\IC{u1} \IC{$\oplus$} \mathbbm{N} \IC{$\otimes$} \IC{I}$, the usual
list functor. The ``application'' relation for the above patch is (isomorphic to):

\begin{displaymath}
\xymatrix{
  1 + \mathbbm{N} \times [ \mathbbm{N} ] \ar[rr]^{\F{s0}} \ar[d]_{\iota_2^\circ} & & 1 + \mathbbm{N} \times [ \mathbbm{N} ] \\
  \mathbbm{N} \times [ \mathbbm{N} ] \ar[r]_{\underline{5}^\circ \times id} 
  & \mathbbm{N} \times [ \mathbbm{N} ] \ar[r]_{\pi_2}
  & [ \mathbbm{N} ] \ar[u]^{\text{in}^\circ} }
\end{displaymath}

\subsection{Examples}

Here we add some more examples of patches over fixpoints. These can be seen
in the respective \texttt{Lab.agda} modules. Here are a few examples of list patches:

\Agda{Report/code/Examples}{Example-list-1}

Previously we had \emph{2-3-Trees} as an example. Here are some patches over them:

\Agda{Report/code/Examples}{Example-2-3-TREE-F-inhabitants}

\Agda{Report/code/Examples}{Example-2-3-tree-full}

The patches we calculate are:

\Agda{Report/code/Examples}{Example-2-3-patches}

Which are normalized to the following patches. Note that it is the 
\IC{A$\otimes$} in \F{r1} that lets us copy \F{k1} and \F{k2} from the \F{2-node} to
the \F{3-node}.

\Agda{Report/code/Examples}{Example-2-3-tree-norm1}

\Agda{Report/code/Examples}{Example-2-3-tree-norm2}

\section{Comparing to the Rose Tree approach}

\begin{withsalt}

\begin{itemize}
  \item By using a list of edit operations, they lose the alignments.

  \item They allow for sharing of data even when the same constructor is used.
\end{itemize}

\end{withsalt}

\appendix
\section{Products in the Kleisli Category}
\label{appendix:productskleisli}

\newcommand{\CAT}[1]{\mathbf{#1}}
\newcommand{\Kleisli}[1]{\mathbf{Kl}(#1)}
\newcommand{\KleiFunct}[1]{{#1}^\flat}
  Given a monad $M : \CAT{C} \rightarrow \CAT{C}$, let $\Kleisli{M}$
be the Kleisli Category of $M$, we denote by $\KleiFunct{\square} :
\CAT{C} \rightarrow \Kleisli{M}$ the \emph{identity on objects}
inclusion functor into the Kleisli of $M$; it's action on arrows is
defined as $\KleiFunct{f} = \eta \cdot f$. We will denote composition
in $\CAT{C}$ by $\cdot$ whereas composition in $\Kleisli{M}$ will be
denoted $\bullet$.

  Coproducts carry trivially as $\KleiFunct{\cdot}$ is a left
adjoint\footnote{ We can define a functor $U : \Kleisli{M} \rightarrow
\CAT{C}$ as $U\;A = M\;A$ and $U\;f = \mu \cdot M\;f$. We have that
$\KleiFunct{\square} \dashv U$.  In fact, this is the initial
adjunction that constructs the monad $M$, $U \cdot \KleiFunct{\square}
= M$! In fact, $U (\KleiFunct{A}) = M\;A$ and $U (\KleiFunct{f}) =
M\;f$. There is a final such adjunction giving rise to the
Eilenberg-Moore construction.  } and, hence, preserve
colimits. Products are not so straight forward.

\newcommand{\lstr}{\tau_l} \newcommand{\rstr}{\tau_r} We can define a
notion of \emph{almost products} if $M$ is commutative, that is, there
exists a left and right strength such that $\lstr \bullet \rstr \equiv
\rstr \bullet \lstr$.  We denote $\lstr \bullet \rstr$ by $\delta$.


If $A \times B$ is a product in $\CAT{C}$ and $M$ is commutative,
$\KleiFunct{A\times B}$ will be the \emph{almost product} in
$\Kleisli{M}$ where $\KleiFunct{\langle f , g \rangle} = \delta \cdot
\langle f , g \rangle$.  Although we have that it is the unique arrow
into the product, it does not satisfy the $\beta$-elimination laws,
that is, $\KleiFunct{(\pi_i \cdot \langle f_1 , f_2 \rangle)}
\not\equiv \KleiFunct{f_i}$. This is because side-effects cannot be
undone.

Nevertheless, for $M = $|Maybe|, we have that $\KleiFunct{(\pi_i \cdot
\langle f_1 , f_2 \rangle)} \preceq \KleiFunct{f_i}$, and this
suffices for pretty much all that we need.

We define the product of two arrows the usual way:

\[ \KleiFunct{(f \times g)} 
  = \KleiFunct{ \langle f \cdot \pi_1 , g \cdot \pi_2 \rangle }
\]

  


\end{document}
