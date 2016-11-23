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

\newcommand{\TODO}[1]{%
\[ \bullet \text{\color{blue} #1} \] }

\newcommand{\warnme}[1]{%
{\color{red} \textbf{$[$} #1 \textbf{$]$}}}

\newtcolorbox{withsalt}%
             {colback=blue!5!white%
             ,colframe=blue!75!black%
             ,fonttitle=\bfseries%
             ,title={Needs discussion:}}

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
  
  The universe we are using is a variant of Regular types,
but instead of having only one type variable, we handle $n$
type variables. The codes are description of regular functors on $n$ variables:

\Agda{RegDiff/Generic/Regular}{U-def}

  Constructor \IC{I} refers to the $n$-th type variable whereas \IC{K} refers
to a constant type. Value \textit{ks\#} is passed as a module parameter.
The denotation is defined as:

\Agda{RegDiff/Generic/Parms}{Parms-def}

\newcommand{\Interp}[2]{\F{$\llbracket$} #1 \F{$\rrbracket$}_{#2}}
\Agda{RegDiff/Generic/Regular}{U-denotation}

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

  I still have no good justification for the \textit{parm-size}
field. Later on I sketch what I believe is the real meaning of the
cost function.

  The following sections discuss functionality that does not depend on
\emph{parameters to codes}.  We will be passing them as Agda module
parameters. The first diffing technique we discuss is the trivial
diff. It's module is declared as follows:

\Agda{RegDiff/Diff/Trivial/Base}{Trivial-module-decl}

  We stick to this nomenclature throughout the code. The first line
handles constant types: \textit{ks\#} is how many constant types we
have, $ks$ is the vector of such types and $keqs$ is an indexed vector
with a proof of decidable equality over such types. The second line
handles type parameters: \textit{parms\#} is how many type-variables our
codes will have, $A$ is the valuation we are using and $WBA$ is a
proof that $A$ is \emph{well behaved}.

  We then declare the following synonyms:

\Agda{RegDiff/Diff/Trivial/Base}{Trivial-defs}

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

   The simplest possible way to describe a transformation is to say
what is the source and what is the destination of such
transformation. This can be accomplished by the Diagonal functor just
fine.

\Agda{RegDiff/Diff/Trivial/Base}{delta-def}

  Now, take an element $(x , y) : \F{$\Delta$}\;ty\;tv$. The ``application''
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
that $(x , y)^\flat \equiv \SingletonRel{x}{y}$ is trivially functional.

\subsection{Spines}
\label{subsec:spines}

  We can try to make it better by identifying the longest prefix of
constructors where $x$ and $y$ agree, before giving up and using \F{$\Delta$}. 
Moreover, this becomes much easier if $x$ and $y$ actually have the same type.
In practice, we are only interested in diffing elements of the same language.
It does not make sense to diff a C source file against a Haskell source file.

Nevertheless, we define an \F{S} structure to capture the longest common prefix
of $x$ and $y$:

\Agda{RegDiff/Diff/Regular/Base}{S-def}

Note that \F{S} makes a functor (actually, a free monad!) on
$P$, and hence, we can map over it:

\Agda{RegDiff/Diff/Regular/Base}{S-map-def}

Computing a spine is easy, first we check whether or not $x$ and
$y$ are equal. If they are, we are done. If not, we inspect the first
constructor and traverse it. Then we repeat.

\Agda{RegDiff/Diff/Regular/Base}{spine-def}

The ``application'' relations specified by a spine $s = \F{spine-cp}\;x\;y$, denoted $s^\flat$ are:

\begin{align*}
  \IC{Scp}^\flat                    &= \hspace{2.3em} \xymatrix{ A & A \ar[l]_{id}} \\
  (\IC{S$\otimes$}\;s_1\;s_2)^\flat &= \xymatrix{ A \times B & A \times B \ar[l]_(.45){s_1^\flat \times s_2^\flat}} \\
  (\IC{Si1}\;s)^\flat               &= \xymatrix{ A + B & A + B \ar[l]_(.45){i_1 \cdot s^\flat \cdot i_1^\circ}} \\                                                   
  (\IC{Si2}\;s)^\flat               &= \xymatrix{ A + B & A + B \ar[l]_(.45){i_2 \cdot s^\flat \cdot i_2^\circ}} \\    
  (\IC{SX}\;(x , y))^\flat          &= \hspace{2.3em} \xymatrix{ A & A \ar[l]_{\SingletonRel{x}{y}} }
\end{align*}

  Note that, in the $(\IC{SX}\;(x , y))$ case, we already assume there is a \F{$\Delta$} there
because $s$ was the output of \F{spine-cp}. In the general case this is slightly different.
The \texttt{Domain} modules are the ones responsible for handling the ``application'' relations.

\begin{withsalt}
  Non-cannonicity can be a problem: $\IC{Scp}^\flat \equiv (\IC{S$\otimes$}\;\IC{Scp}\;\IC{Scp})^\flat$
  Even though the \F{spine-cp} function will never find the right-hand above, 
  it feels sub-optimal to allow this.

  One possible solution could be to remove \IC{Scp} and handle them through
  the maybe monad. Instead of (\F{S}\;\F{$\Delta$}) we would have (\F{S}\;(\F{Maybe}\;\F{$\Delta$})),
  where the \IC{nothing}s represent copy. This ensures that we can only copy on the leaves.
  Branch \texttt{explicit-cpy} of the repo has this experiment going. It is easier said
  than done.
\end{withsalt}

Ignoring the problems and moving forward; note that for any $x$ and
$y$, a spine $s = \F{spine-cp}\;x\;y$ will NEVER contain a product nor
a unit on a leaf (we force going through products and copying units).
Hence, whenever we are traversing $s$ and find a $\IC{SX}$, we know
that: (1) the values of the pair are different and (2) we must be at a
coproduct, a constant type or a type variable. The constant type or
the type variable are out of our control. But we can refine our
\emph{description} in case we arrive at a coproduct.

\subsection{Coproduct Changes}
\label{subsec:changes}

%format i1 = "\IC{i1}"
%format i2 = "\IC{i2}"
  Let's imagine we are diffing the following values of a type $\mathbbm{1} + (\mathbbm{N}^2 + \mathbbm{N})\times \mathbbm{N}$:
\begin{align*}
  s & = \F{spine-cp}\;(|i2 (i1 (4 , 10) , 5)|)\;(|i2 (i2 10 , 5)|) \\
    & = \IC{Si2}\; (\IC{S$\otimes$}\; (\IC{SX}\; (|i1 (4 , 10)| , |i2 10|))\; \IC{Scp})
\end{align*}

  And now, we want to \F{S-map} over $s$ and refine the \F{$\Delta$} inside. We want to have information
about which injections we need to pattern match on and which we need to introduce. 
We begin with a type (that's also a free monad) that encodes the injections we need to insert
or pattern-match on:

\Agda{RegDiff/Diff/Regular/Base}{C-def}

Note that \F{C} is also a functor on $P$:

\Agda{RegDiff/Diff/Regular/Base}{C-map-def}

And we make an eager function that will consume ALL coproduct injections from both source
and destination:

\Agda{RegDiff/Diff/Regular/Base}{change-def}

Now, we could \F{S-map} \F{change} over $s$:

\begin{align*}
  \F{S-map}\; \F{change} \; s 
    & = \IC{Si2}\; (\IC{S$\otimes$}\; (\IC{SX}\; (\IC{Ci2}\;(\IC{Ci1$^\circ$} \; (\IC{CX} \; ((4 , 10) , 10)))\; \IC{Scp}) \\
    &= s'
\end{align*}


The whole thing also becomes of a much more expressive type:

\begin{align*}
 s'= \F{S-map}\; \F{change} \; s &: \F{S}\;(\F{C}\;\F{$\Delta$})
\end{align*}

We can read the type as: a common prefix from both terms followed by injections into the target term and
pattern matching on the source term followed by point-wise changes from source to destination. 

  Note that we can also say, for sure, that we will never have a $\IC{SX}\;(\IC{Ci1}\;(\IC{Ci1$^\circ$}\;c))$
at the S-leaves of $s'$; this would mean that we need to inject the target with $\iota_1$ and
pattern match the source on $\iota_1$, but this is a common-prefix! Hence it would be recognized
by \F{spine-cp} and instead we would have: $\IC{Si1}\;(\IC{SX}\;c)$.

\begin{withsalt}
  Even though the algorithm does not produce $\IC{SX}\;(\IC{Ci1}\;(\IC{Ci1$^\circ$}\;c))$, as mentioned
  above, this is still a valid inhabitant of $\F{S}\;(\F{C}\;\F{$\Delta$})$!
\end{withsalt}

Just like the values of \F{S}, we can also define the ``application'' relation induced by the 
values of \F{C}:

\begin{align*}
  (\IC{Ci1}\;c)^\flat &= \xymatrix{ B + X & A \ar[l]_(.3){\iota_1 \cdot c^\flat}} \\
  (\IC{Ci2}\;c)^\flat &= \xymatrix{ X + B & A \ar[l]_(.3){\iota_2 \cdot c^\flat}} \\                                                   
  (\IC{Ci1$^\circ$}\;c)^\flat &= \hspace{2.3em} \xymatrix{ B & A + X \ar[l]_(.5){c^\flat \cdot \iota_1^\circ}} \\
  (\IC{Ci2$^\circ$}\;c)^\flat &= \hspace{2.3em} \xymatrix{ B & X + A \ar[l]_(.5){c^\flat \cdot \iota_2^\circ}} \\   
  (\IC{CX}\;(x , y))^\flat          &= \hspace{2.3em} \xymatrix{ B & A \ar[l]_{\SingletonRel{x}{y}} }
\end{align*}


Note that up until now, everything was deterministic! This is something we are about to lose.

\subsection{Aligning Everything}
\label{subsec:align}

Following a similar reasoning as from \F{S} to \F{C}; the leaves of a \F{C} produced through
\F{change} will NEVER contain a coproduct as the topmost type. Hence, we know that they will contain
either a product, or a constant type, or a type variable. In the case of a constant type
or a type variable, there is not much we can do at the moment, but for a product we can 
refine this a little bit more before using \F{$\Delta$}\footnote{%
In fact, splitting the different stages of the algorithm into different types reinforced
our intuition that the alignment is the source of difficulties. As we shall see, we now need
to introduce non-determinism.}.

Looking at our running example, we have a leaf $(\IC{CX} \; ((4 , 10) , 10))$ to take care of.
Here the source type is $\mathbbm{N}^2$ and the destination is $\mathbbm{N}$. Note that
the $\mathbbm{N}$ is treated as a constant type here. As we mentioned above, we have a product
on the source, so we could extract some more information before giving up and using \F{$\Delta$}!

Here is where our design space starts to be huge. Our definition of alignment is:

\Agda{RegDiff/Diff/Regular/Base}{Al-def}

Which states that we can force components of the source or destination product to be
equal to a given value or we can join two alignments together (This is a big source of inefficiency!).

Computing alignments is very expensive! In the case we actually have products on both the
source and the destination we have a lot of options (hence the list monad!):

\Agda{RegDiff/Diff/Regular/Base}{align-all-paths-def}

If we only have products on the left or on the right (or none), 
we have less options:

\Agda{RegDiff/Diff/Regular/Base}{align-rest-def}

Following our previous example, we could \F{C-mapM} our alignment function (the \F{C-mapM} is the monadic
variant of \F{C-map}) on $s'$, in order to find all alignments of $(4 , 10)$ and $10$. In this case,
this is very easy\footnote{%
It might be hard to build intuition for why we need the \IC{$A\otimes$} constructor.
On the \texttt{Lab} module of Fixpoint there is an example using 2-3-Trees that motivates the
importance of that constructor}.

\begin{align*}
  \F{C-map}\;\F{align}\;s' = & [ \; \IC{Si2}\; (\IC{S$\otimes$}\; (\IC{SX}\; (\IC{Ci2}\;(\IC{Ci1$^\circ$}\;(\IC{CX} \; (\IC{Ap1$^\circ$}\; 10\; (\IC{AX} \; (4 , 10)))))\; \IC{Scp}) \\
                                    & , \; \IC{Si2}\; (\IC{S$\otimes$}\; (\IC{SX}\; (\IC{Ci2}\;(\IC{Ci1$^\circ$}\;(\IC{CX} \; (\IC{Ap2$^\circ$}\; 4\; (\IC{AX} \; (10 , 10)))))\; \IC{Scp}) \; ]
\end{align*}

If we ommit the \IC{SX} and \IC{CX} constructors this becomes slightly more readable:

\begin{align*}
  \F{C-map}\;\F{align}\;s' = & [ \; \IC{Si2}\; (\IC{S$\otimes$}\; (\IC{Ci2}\;(\IC{Ci1$^\circ$}\;(\IC{Ap1$^\circ$}\; 10\; (\IC{AX} \; (4 , 10)))))\; \IC{Scp}) \tag{P1} \\
                                    & , \; \IC{Si2}\; (\IC{S$\otimes$}\; (\IC{Ci2}\;(\IC{Ci1$^\circ$}\;(\IC{Ap2$^\circ$}\; 4\; (\IC{AX} \; (10 , 10)))))\; \IC{Scp}) \; ] \tag{P2}
\end{align*}

  But now we end up having to choose between one of those to be \emph{the} patch. This is where we start to need a cost function.
Before talking about cost, let's look at the ``application'' relations of \F{Al}:

\begin{align*}
  (\IC{A$\otimes$}\;a_1\;a_2)^\flat &= \xymatrix@@C=5em{ B \times D & A \times C \ar[l]_{a_1^\flat \times a_1^\flat}} \\
  (\IC{Ap1}\;x\;c)^\flat &= \xymatrix@@C=5em{ B \times X & A \ar[l]_{< c^\flat , \underline{x} >}} \\
  (\IC{Ap2}\;x\;c)^\flat &= \xymatrix@@C=5em{ X \times B & A \ar[l]_{< \underline{x} , c^\flat  >}} \\ 
  (\IC{Ap1$^\circ$}\;x\;c)^\flat &= \hspace{2.3em} \xymatrix@@C=5em{ B & A \times X \ar[l]_{\pi_1 \cdot (c^\flat \times \underline{x}^\circ) }} \\
  (\IC{Ap2$^\circ$}\;x\;c)^\flat &= \hspace{2.3em} \xymatrix@@C=5em{ B & X \times A \ar[l]_{\pi_2 \cdot (\underline{x}^\circ \times c^\flat)}} \\   
  (\IC{AX}\;(x , y))^\flat          &= \hspace{2.3em} \xymatrix@@C=5em{ B & A \ar[l]_{\SingletonRel{x}{y}} }
\end{align*}

\section{Patches as Relations}

On Section \ref{subsec:spines} we mentioned that the copy constructor was problematic. Another motivation for removing
it and handling everything externally is that we would like to say that the patch (P2) above copies the 10, instead
of saying that 10 changes into 10. We can postpone this by changing the relation semantics of \F{$\Delta$}. We can say
that: $(x , x)^\flat = id$ and $(x , y)^\flat = \SingletonRel{x}{y}$.

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

Nevertheless, it is clear which patch we should choose! We should always choose the patch that
gives rise to the biggest relation, as this is applicable to much more elements.

This suggests an interesting justification for the cost function. For some reason, looks like we won the lottery with our cost functions.
We are always choosing the patch that gives rise to the maximal relation. I still don't clearly understand why or how,
but it works.

Below are our cost functions:

\Agda{RegDiff/Diff/Trivial/Base}{Trivial-cost-def}

\Agda{RegDiff/Diff/Regular/Base}{S-cost-def}

\Agda{RegDiff/Diff/Regular/Base}{C-cost-def}

\Agda{RegDiff/Diff/Regular/Base}{Al-cost-def}

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
make sure we exploit products. We kept mentioning that we could not do anything
on the leaves that were type variables or constant types. Well, constant types
we still can't, and we have to stick to \F{$\Delta$}, but now we need to handle
the type-variables.

A patch for a fixed point might not follow the precise order of operations (\F{S}, then \F{C}, then \F{Al})
that regular types enjoyed. For instance, imagine we are transforming the following
lists:

\[
  [5 , 8 , 13 , 21] \rightsquigarrow [8 , 13 , 21]
\]

Let lists be seen (as usual) as the initial algebras of $L_A\;X = 1 + A\times X$;
then, both lists are inhabitants of $\mu L_{\mathbbm{N}}$, but, more precisely,
the source is an inhabitant of $L_{\mathbbm{N}} (L_{\mathbbm{N}} (L_{\mathbbm{N}} (L_{\mathbbm{N}}\; \mathbbm{1})))$
whereas the target is an inhabitant of $L_{\mathbbm{N}} (L_{\mathbbm{N}} (L_{\mathbbm{N}}\; \mathbbm{1}))$.

Here, we are already beginning with different types, so a spine (which is homogeneous) might not
be the best start! In fact, the best start is to say that the first $5$ is deleted, then the spine
can kick in and say that everything else is copied!

Here is the definition:

\Agda{RegDiff/Diff/Multirec/Base}{Patchmu-def}

The \IC{skel} constructor lets a spine kick in, which has \F{Patch$\mu$} on it's leaves again.
The \IC{fix} constructor ties the know between type-variables and their lookup in the family, which
is isomorphic. The \IC{set} constructor specifies that we are setting something.
The \F{C$\mu$} type extends the previous \F{C} with options for inserting and deleting:

\Agda{RegDiff/Diff/Multirec/Base}{Patchmu-aux-def}

Note that \IC{fix}, \IC{Cins} and \IC{Cdel} are heterogeneous on the \F{Fam$_i$} indexes! This is
very important for mutually recursive families.

\begin{withsalt}
  I have been experimenting with different cost models and slight variations on
  the definitions of \F{Patch$\mu$}. I found that requiring \IC{set} to set the \emph{same}
  type is a great idea! Not only it removes a lot of absurd patches, but it also 
  speeds up the process quite a bit:

%format Delta = "\Delta"
%format Patchmu = "Patch\mu"
  | set : {ty : U} -> Delta ty ty -> Patchmu ty ty |
\end{withsalt}

Computing a \F{Patch$\mu$} is done by piggybacking on the functions for computing \F{S}, \F{C} and \F{Al}
separately, then mapping over them with some refinement functions:

\Agda{RegDiff/Diff/Multirec/Base}{diffmu-non-det}

The refinement functions are given by:

\Agda{RegDiff/Diff/Multirec/Base}{diffmu-refinements}

Obviously, we can also define the ``application'' relation for fixed points, and that
is done in \texttt{RegDiff/Diff/Multirec/Domain}. I believe it is more worthwhile to
look at some example patches and their ``application'' relation instead of the general
case, though. Let's begin with the lists we just discussed:

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
