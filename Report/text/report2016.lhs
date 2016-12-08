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
type variables and constant types have a different \emph{type} than the
codes for types. This requires more discipline to organize our code. Nevertheless,
we may wish to see \F{Atom}s as a trivial \emph{Sum-of-Product}.

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
have decidable equality for $A\;k$ and some mapping from $A\;k$ to
$\mathbb{N}$ for all $k$.  We call such valuations a
\emph{well-behaved parameter}:

\Agda{RegDiff/Generic/Parms}{WBParms-def}

\begin{TODO}
  The field \emph{parm-size} is not really needed anymore!
  Remove it!
\end{TODO}

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
codes will have, $A$ is the valuation we are using and $WBA$ is a
proof that $A$ is \emph{well behaved}.

\begin{TODO}
  Now parameters are setoids, we can drop out the WBA record.
\end{TODO}

  Below are the synonyms we use for the rest of the code:

\Agda{RegDiff/Diff/Trivial/Base}{Trivial-defs}

\Agda{RegDiff/Diff/Trivial/Base}{Trivial-aux-defs}

\section{Computing and Representing Patches}

  Intuitively, a \textit{Patch} is some description of a
transformation. Setting the stage, let $A$ and $B$ be a types, $x : A$
and $y : B$ elements of such types.  A \emph{patch} between $x$ and
$y$ must specify a few parts:

\begin{enumerate}[i)]
  \item An $apply_p : A \rightarrow Maybe\;B$ function, 
  \item such that $apply_p\;x \equiv \IC{just}\;y$.
\end{enumerate}

Well, $apply_p$ can be seen as a functional relation ($R$ is functional iff $img\;R\subseteq id$)
from $A$ to $B$. We call this the ``application'' relation of the patch, and we will denote it
by $p^\flat \subseteq A \times B$.

\begin{withsalt}
  There is still a lot that could be said about this. I feel like $p^\flat$ should
also be invertible in the sense that:
\begin{enumerate}[i)]
  \item Let $(\text{inv}\;p)$ denote the inverse patch of $p$, which is a patch from $B$ to
        $A$.
  \item Then, $p^\flat \cdot (\text{inv}\;p)^\flat \subseteq id$ 
          and $(\text{inv}\;p)^\flat \cdot p^\flat \subseteq id$,
        Assuming $(\text{inv}\;p)^\flat$ is also functional, we can use
        the maybe monad to represent these relations in $\mathbf{Set}$.
        Writing the first equation on a diagram in $\mathbf{Set}$,
        using the $apply$ functions:
\begin{displaymath}
\xymatrix@@C=5em{ B \ar[r]^{apply_{(\text{inv}\;p)}} \ar[drr]_{\iota_1}
         & A + 1 \ar[r]^{apply_p + id} & (B + 1) + 1 \ar[d]_{\mu} \\
         & & B + 1}
\end{displaymath}
  \item This is hard to play ball with. We want to say, in a way, that
        $x\;(p^\flat)\;y$ iff $y\;((\text{inv}\;p)^\flat)\;x$.
        That is, $(\text{inv}\;p)$ is the actual inverse of $p$.
        Using relations, one could then say that $(\text{inv}\;p)^\flat$ is the
        converse of $(p^\flat)$. That is: $(\text{inv}\;p)^\flat \equiv (p^\flat)^\circ$.
        But, if $(\text{inv}\;p)^\flat$ is functional, so is $(p^\flat)^\circ$.
        This is the same as saying that $p^\flat$ is entire!
        If $p^\flat$ is functional and entire, it is a function (and hence, total!). 
        And that is not true.
\end{enumerate}
\end{withsalt} 

   Now, let us discuss some code and build some intuition for what is
what in the above schema. We will present different parts of the code,
how do they relate to this relational view and give examples here and there!

\subsection{Trivial Diff}
\label{subsec:trivialdiff}
%format (REL p)       = p "^\flat"
%format (CONST x)     = "\underline{" x "}"
%format .             = "\cdot"
%format (CONV x)      = x "^\circ"
%format *             = "\times"
%format (SINGLR x y)  = "\SingletonRel{" x "}{" y "}"
%format (SPLIT (a) (b)) = "\langle {" a "} , {" b "} \rangle"
%format inj1          = "\IC{$\iota_1$}"
%format inj2          = "\IC{$\iota_2$}"
%format injI          = "\IC{inj}_i"
%format injJ          = "\IC{inj}_j"
%format pi1           = "\IC{$\pi_1$}"
%format pi2           = "\IC{$\pi_2$}"


%format Delta = "\F{$\Delta$}"
%format DeltaS = "\F{$\Delta_s$}"
%format DeltaA = "\F{$\Delta_a$}"
%format DeltaP = "\F{$\Delta_p$}"

   The simplest possible way to describe a transformation is to say
what is the source and what is the destination of such
transformation. This can be accomplished by the Diagonal functor, |Delta|, just
fine.

  Now, take an element |(x , y) : Delta ty tv|. The ``application''
relation it defines is trivial: $ \{ (x , y) \} $, or, in PF style:

\newcommand{\SingletonRel}[2]{\underline{#2} \cdot \underline{#1}^\circ}
\begin{displaymath}
\xymatrix{
  \Interp{ty}{A} \ar@@/^2.0pc/[rr]^{\SingletonRel{x}{y}} 
  & K \ar[l]^{\underline{x}} \ar[r]_{\underline{y}} & \Interp{tv}{A} 
}
\end{displaymath}

  Where, for any $A , B \in Set$ and $x : A$, $\underline{x} \subseteq A \times B$ 
represents the \emph{everywhere} $x$ relation, defined by
\[
 \underline{x} = \{ (x , b) \mid b \in B \}
\]

  This is a horrible patch however: We can't calculate with it because
we don't know \emph{anything} about \emph{how} $x$ changed into $y$. Note, however,
that | REL (x , y) == (SINGLR x y) | is trivially functional.

\begin{withsalt}
  In the code, we actually define the ``application'' relation of |Delta|
as:

\begin{align*}
  |REL (x , x)| &= |id| \\
  |REL (x , y)| &= |SINGLR x y|
\end{align*}

  This suggests that copies might be better off being handled by
the trivial diff. We will return to this discussion in section \ref{sec:patchesasrelations}
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
%format ddd = "\cdots"

%format spine-cp = "\F{spine-cp}"
%format spine    = "\F{spine}"
%format S        = "\F{S}"
%format S-map    = "\F{S-map}"
%format Maybe    = "\F{Maybe}"
%format just     = "\IC{just}"
%format nothing  = "\IC{nothing}"


  We can make the trivial diff better by identifying whether or not
$x$ and $y$ agree on something! In fact, we will aggresively look for copying
oportunities. We start by checking if $x$ and $y$ are, in fact, equal. If they are,
we say that the patch that transforms $x$ into $y$ is \emph{copy}. If they are not equal,
they might have the same \emph{constructor}. If they do, the say that the constructor
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

\Agda{RegDiff/Diff/Regular/Base}{zip-product-def}

The ``application'' relations specified by a spine |s = spine x y|, 
denoted |REL s| are defined by:

\begin{align*}
  |REL Scp|           &= \hspace{3em} \xymatrix@@C=10em{ A & A \ar[l]_{id}} \\
  |REL (SX p)|        &= \hspace{3em} \xymatrix@@C=10em{ A & A \ar[l]_{|REL p|} } \\
  |REL (Scns i [s1 , ddd , sN])|   
                 &= \xymatrix@@C=10em{ \amalg_k \Pi_j A_{kj} & \amalg_k \Pi_j A_{kj} 
                                    \ar[l]_{|injI . ((REL s1) * ddd * (REL sN)) . (CONV injI)|}}
\end{align*}

  where |injI| is the injection, with constructor $i$, into $\amalg_k T_k$. It corresponds
to the relational lifting of function \F{injection}.

  Note that, in the |(SX p)| case, we simply ask for the ``application'' relation
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

\[
  |S-map change s|
      = | SX (CX Node2 Node3 ((10 , unit , unit) , (10 , unit , unit , unit))) | \]

  The ``application'' relation induced by |C| is trivial:

\begin{displaymath}
\xymatrix{  V  &  T \ar[l]_{|(REL (CX i j p))|} \ar[d]^{|(CONV injI)|}  \\
            \F{typeOf}\;V\;j \ar[u]^{|injJ|} & \F{typeOf}\;T\;i \ar[l]^{|(REL p)|}
         }
\end{displaymath}

Note that up until now, everything was deterministic! This is something we are bound to lose
when talking about alignment.

\subsection{Aligning Everything}
\label{subsec:align}
%format Atimes = "\IC{A$\otimes$}"
%format Ap1    = "\IC{Ap1}"
%format Ap2    = "\IC{Ap2}"
%format Ap1o   = "\IC{Ap1$^\circ$}"
%format Ap2o   = "\IC{Ap2$^\circ$}"
%format AX     = "\IC{AX}"

%format align      = "\F{align}"
%format align-exp  = "\F{align-exp}"
%format Al      = "\F{Al}"
%format Al-mapM = "\F{Al-mapM}"

%format a1 = "a_1"
%format a2 = "a_2"


Looking at our running example, we have a leaf |(CX ((4 , 10) , 10))| to take care of.
Here the source type is $\mathbbm{N}^2$ and the destination is $\mathbbm{N}$. Note that
the $\mathbbm{N}$ is treated as a constant type here. As we mentioned above, we have a product
on the source, so we could extract some more information before giving up and using |Delta|!

\end{document}

\subsubsection{A Parenthesis}

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
a map. We would like, however, that our definition have a maximal domain, that is, we require
impose the least possible amount of restrictions. In this case, we can actually define $a$ 
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

\subsubsection{Back to Agda}

We will look at alignments from the ``finding a map between products'' perspective.
Here is where our design space starts to be huge, and so, we should start making
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

The following datatype describe such maps:

\Agda{RegDiff/Diff/Regular/Base}{Al-def}

Computing alignments is very expensive, specially if done in the naive way.
Nevertheless, we present the naive alignment first, and gistinguish it with an \emph{exp} suffix.
In the case we actually have products on both the source and the destination 
we have a lot of options (hence the list monad!):

\Agda{RegDiff/Diff/Regular/Base}{align-exp-all-paths-def}

If we only have products on the left or on the right (or none), 
we have less options:

\Agda{RegDiff/Diff/Regular/Base}{align-exp-rest-def}

Let's come back to our running example! 
Following the previous trend, we could \F{C-mapM} our alignment function (the |C-mapM| is the monadic
variant of |C-map|) on $s'$, in order to find all alignments of $(4 , 10)$ and $10$. In this case,
this is very easy\footnote{%
It might be hard to build intuition for why we need the |Atimes| constructor.
On the \texttt{Lab} module of Fixpoint there is an example using 2-3-Trees that motivates the
importance of that constructor}.

\begin{align*}
  |C-map align s'| = & | [ Si2 (Stimes (SX (Ci2 (Ci1o (CX (Ap1o 10 (AX (4 , 10))))))) Scp)    | \\
                     & | , Si2 (Stimes (SX (Ci2 (Ci1o (CX (Ap2o 4  (AX (10 , 10))))))) Scp) ] |
\end{align*}

If we ommit the |SX| and |CX| constructors this becomes slightly more readable:

\begin{align*}
  |C-map align s'| = & | [ Si2 (Stimes (Ci2 (Ci1o (Ap1o 10 (AX (4 , 10))))) Scp)    | \\
                     & | , Si2 (Stimes (Ci2 (Ci1o (Ap2o 4  (AX (10 , 10))))) Scp) ] |
\end{align*}

  But now we end up having to choose between one of those to be \emph{the} patch. This is where we start to need a cost function.
Before talking about cost, let's look at the ``application'' relations of |Al|:

\begin{align*}
  | REL (Atimes a1 a2)| &= \xymatrix@@C=5em{ B \times D & A \times C \ar[l]_{|(REL a1) * (REL a2)|}} \\
  | REL (Ap1 x a)|      &= \xymatrix@@C=5em{ B \times X & A \ar[l]_{| SPLIT (REL a) (CONST x) |}} \\
  | REL (Ap2 x a)|      &= \xymatrix@@C=5em{ X \times B & A \ar[l]_{| SPLIT (CONST x) (REL a)|}} \\ 
  | REL (Ap1o x a)|     &= \hspace{2.3em} \xymatrix@@C=5em{ B & A \times X \ar[l]_{ |pi1 . ((REL a) * (CONV (CONST x)))| }} \\
  | REL (Ap2o x a)|     &= \hspace{2.3em} \xymatrix@@C=5em{ B & X \times A \ar[l]_{ |pi2 . ((CONV (CONST x)) * (REL a))| }} \\   
  | REL (AX p))|        &= \hspace{2.3em} \xymatrix@@C=5em{ B & A \ar[l]_{ |REL p| } }
\end{align*}

Note how |Ap1o| and |Ap2o| force a component of the source to be equal to something (that's equivalent to
pattern matching on the source) whereas |Ap1| and |Ap2| set a component of the destination to
be equal to something. Let us represent the $f$ we devised on the $\mathcal{DNA}$ example using |Al|.
Recall $f \;(C , x , y , C , z) = (x , A , y , A , z , T)$.

%format bC = "C"
| f == Ap2o bC (Atimes Scp (Ap2 A (Atimes Scp (Atimes (AX (bC , A)) (Ap1 T Scp))))) |

\begin{TODO}

 Yet... for some reason, our simple optimization below is not finding the above
  alignment... we need to fix it!

 I can see Tarmo's coalgebras for sharing working wonders in computing
 these alignments in linear time.

\end{TODO}

\subsection{A simple optimization}

\begin{withsalt}

  Looking carefully at the \F{align-exp} function above, we are computing
a lot of unecessary branches, specially in the case for products
on both sides. Below we compute |align-exp (x , y) (w , z)| and
put arrows indicating which \F{Al} have an isomorphic underlying
``application'' relation.

\begin{displaymath}
\xymatrix@@R=.5em@@C=.05em{%
  |align-exp (x,y) (w,z)| 
   &  & |= Atimes (AX (x , w)) (AX (y , z))| & \\
   &  & |CONS Ap1  z (Ap1o y (AX (x , w)))| & \ar@@/_2em/[u] \\
   &  & |CONS Ap1  z (Ap2o x (AX (y , w)))| & \\
   &  & |CONS Ap2  w (Ap1o y (AX (x , z)))| & \\
   &  & |CONS Ap2  w (Ap2o x (AX (y , z)))| & \ar@@/_2em/[uuuu] \\
   &  \ar@@/^2em/[uuuu] & |CONS Ap1o y (Ap1  z (AX (x , w)))| & \\
   &  \ar@@/^2em/[uuuu] & |CONS Ap2o x (Ap1  z (AX (y , w)))| & \\
   &  \ar@@/^2em/[uuuu] & |CONS Ap1o y (Ap2  w (AX (x , z)))| & \\
   &  \ar@@/^2em/[uuuu] & |CONS Ap2o x (Ap2  w (AX (y , z)))| & \\
   & & |CONS NIL|
}                  
\end{displaymath}

If we then look at which |Al|ignments do \emph{not} have an arrow out of it, that
is, the ones that don't have an isomorphic alignment also being computed, we get:

\begin{align*}
  |align (x , y) (w , z)|
    & |= Atimes (AX (x , w)) (AX (y , z))| \\
    & |CONS Ap1  z (Ap2o x (AX (y , w)))| \\
    & |CONS Ap2  w (Ap1o y (AX (x , z)))| \\
    & |CONS NIL|
\end{align*}

\end{withsalt}
\begin{withsalt}

We hence simplify the alignment function:

\Agda{RegDiff/Diff/Regular/Base}{align-all-paths-def}

\vspace{-.7em}

\Agda{RegDiff/Diff/Regular/Base}{align-rest-def}

The \F{kill-p2} (resp. \F{kill-p1}) functions above are used to prune the search space
further. They will ignore every branch that starts with a |Ap2| (resp |Ap1|), which
will, for sure, have had an isomorphic alignment computed already (in terms of |Atimes|).
Writing down the ``application'' relations makes this easy to see.

\end{withsalt}

\section{Patches as Relations}
\label{sec:patchesasrelations}

Here we will be using the semantics for |REL (x , y)| as described in
the discussion box at Section~\ref{subsec:trivialdiff}.  That is, we
would like to say that the patch (P2), above, copies the 10, instead
of saying that 10 changes into 10.  We can postpone this by changing
the relation semantics of \F{$\Delta$}.  Hence: $(x , x)^\flat` = id$
and $(x , y)^\flat = \SingletonRel{x}{y}$.

Nevertheless, if we look at the two patches above as relations, we have:

\begin{align*}
  P1^\flat & = i_2 \cdot (i_2 \cdot < \SingletonRel{10}{4} , \underline{10} >^\circ \cdot i_1^\circ \times id) \cdot i_2^\circ \\
  P2^\flat & = i_2 \cdot (i_2 \cdot < \underline{4} , id >^\circ \cdot i_1^\circ \times id) \cdot i_2^\circ
\end{align*}

Writing them in a diagram:

\newcommand{\NAT}{\mathbbm{N}}
\newcommand{\UNIT}{\mathbbm{1}}
\begin{displaymath}
\xymatrix{%
 & \NAT \ar[d]_{id} \\ 
 & \NAT \ar[rrd]^(0.3){\pi_1^\circ} & & (\NAT^2 + \NAT) \times \NAT \ar[llu]_{\pi_1} \ar[lld]^(0.2){\pi_2} 
 & \UNIT + (\NAT^2 + \NAT) \times \NAT \ar[l]_{i_2^\circ} \ar@@{-->}@@<-.6ex>[d]_{P2^\flat} \ar@@{-->}@@<.6ex>[d]^{P1^\flat}\\
 \NAT^2 \ar@@<-.6ex>[d]_{<\underline{4} , id>^\circ} \ar@@<.6ex>[d]^{< \SingletonRel{10}{4} , \underline{10} >^\circ} 
 & \NAT^2 + \NAT \ar[l]_{i_1^\circ} & & (\NAT^2 + \NAT) \times \NAT \ar[r]_{i_2} & \UNIT + (\NAT^2 + \NAT) \times \NAT  \\
 \NAT \ar[r]_{i_2} & \NAT^2 + \NAT \ar[rru]_{\pi_2^\circ}
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

This suggests an interesting justification for the cost function. For
some reason, looks like we won the lottery with our cost functions.
We are always choosing the patch that gives rise to the maximal
relation. I still don't clearly understand why or how, but it works.

\begin{TODO}

Below are our cost functions:

we should actually be able to choose patches without cost functions...
discuss this up! Use the |align| optimization example...

ADD VALUES, FORGET ABOUT THOSE RAW FUNCTIONS!

\Agda{RegDiff/Diff/Trivial/Base}{Trivial-cost-def}

\Agda{RegDiff/Diff/Regular/Base}{S-cost-def}

\Agda{RegDiff/Diff/Regular/Base}{C-cost-def}

\Agda{RegDiff/Diff/Regular/Base}{Al-cost-def}

\end{TODO}

\subsection{Patches for Regular Types}

Now that we have \emph{spines}, \emph{changes} and \emph{alignments}
figured out, we can define a patch as:

\Agda{RegDiff/Diff/Regular/Base}{Patch-def}

Computing inhabitants of such type is done with:

\Agda{RegDiff/Diff/Regular/Base}{diff1-nondet-def}

\section{Mutually Recursive Types}

Now that we have a clear picture of regular types, 
extending this to recursive types is not
very difficult.

First, recall that a mutually recursive family is defined as $n$ codes that
each reference $n$ type variables:

\Agda{RegDiff/Generic/Multirec}{Fam-def}

\Agda{RegDiff/Generic/Multirec}{Fix-def}

Another auxiliary definition we use here is the indexed coproduct, which let's us \emph{extend}
some indexed type.

\Agda{RegDiff/Diff/Multirec/Base}{UUSet-coprod}

Now, we already have the ingredients for common prefixes, coproducts and
products. We now need to handle type variables. Before we proceed with the nasty
definitions, we still need two last synonyms:

\Agda{RegDiff/Diff/Multirec/Base}{Fami-def}

Here $\F{T}\;k$ represents the $k$-th type of the family, and \F{Fam$_i$} represents
the indexes of our family. 

Remember that we have \F{S}pines, to handle the common prefixes; \F{C}hanges to
handle different coproduct injections on source and destination and \F{Al}ignments to
make sure we exploit product structure. We kept mentioning that we could not do anything
on the leaves that were type variables or constant types. Well, constant types
we still can't, and we have to stick to \F{$\Delta$}, but now we need to handle
the type-variables since they are used to tie the recursion knot.

A patch for a fixed point might not follow the precise order of
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

Here is the definition:

\Agda{RegDiff/Diff/Multirec/Base}{Patchmu-def}

The \IC{fix} constructor ties the know between type-variables and
their lookup in the recursive family, which is isomorphic. The
\IC{set} constructor specifies that we are setting something. Note that
we require the source and destination types to be equal here!

\begin{withsalt}
  Experimenting with this, I found out that set is only used for constant types
(as expected!). A proof of this would be great.
\end{withsalt}

\F{C$\mu$} type extends the previous \F{C} with the usual edit operations
everyone talks about: modify, delete or insert!

\Agda{RegDiff/Diff/Multirec/Base}{Patchmu-aux-def}

Note how insertions (resp. deletions) happen by \emph{changing and aligning} a type-variable into a type
(resp. a type into a type-variable). Note also that \IC{fix}, \IC{Cins} and \IC{Cdel} are heterogeneous 
on the \F{Fam$_i$} indexes! This is very important for mutually recursive families.

The modifications, therefore, happen when we can take a spine before changing and aligning
something.

Computing a \F{Patch$\mu$} is done by piggybacking on the functions for computing \F{S}, \F{C} and \F{Al}
separately, then mapping over them with some refinement functions:

\Agda{RegDiff/Diff/Multirec/Base}{diffmu-non-det}

The refinement function is easy. We just need to make sure we have
equal source and destination types before we \IC{set} something; otherwise
we simply prune that branch out. This makes the code much more efficient as
we are not trying to \IC{set} an integer into a list.

\Agda{RegDiff/Diff/Multirec/Base}{diffmu-refinements}

Obviously, we can also define the ``application'' relation for fixed points, and that
is done in \texttt{RegDiff/Diff/Multirec/Domain}. I believe it is more worthwhile to
look at some example patches and their ``application'' relation instead of the general
case, though. Let's begin with the lists we just discussed:

\begin{TODO}
  recompile the examples
\end{TODO}

\end{document}

\Agda{Report/code/Examples}{Example-list-2}

Here, \F{LIST-F} is defined as $\IC{u1} \IC{$\oplus$} \mathbbm{N} \IC{$\otimes$} \IC{I}$, the usual
list functor. The ``application'' relation for the above patch is:

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

Previously we also mentioned that \emph{2-3-Trees} were a good motivation for the \IC{A$\otimes$} 
constructor. Here is the actual example (the full code follows to illustrate how modules are imported
and used):

\Agda{Report/code/Examples}{Example-2-3-tree-full}

The patches we calculate are:

\Agda{Report/code/Examples}{Example-2-3-patches}

Which are normalized to the following patches. Note that it is the 
\IC{A$\otimes$} in \F{r1} that lets us copy \F{k1} and \F{k2} from the \F{2-node} to
the \F{3-node}.

\Agda{Report/code/Examples}{Example-2-3-tree-norm1}

\Agda{Report/code/Examples}{Example-2-3-tree-norm2}

\end{document}
