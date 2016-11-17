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

\Agda{RegDiff/Generic/Regular}{U-denotation}

  A mutually recursive family can be easily encoded
in this setting. All we need is $n$ types that refer to $n$ type-variables
each!

\Agda{RegDiff/Generic/Multirec}{Fam-def}

\Agda{RegDiff/Generic/Multirec}{Fix-def}

  This universe is enough to model Context-Free grammars, and hence, provides
the basic barebones for diffing elements of an arbitrary programming language.
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

\newcommand{\Interp}[2]{\F{$\llbracket$} #1 \F{$\rrbracket$}_{#2}}
  In the following sections, we will be dealing with values of
$\Interp{ty}{A}$ for some class of valuations $A$, though.  We need to
have decidable equality for $A\;k$ and some mapping from $A\;k$ to
$\mathbb{N}$ for all $k$.  We call such valuations a
\emph{well-behaved parameter}:

\Agda{RegDiff/Generic/Parms}{WBParms-def}

  I still have no good justification for the \textit{parm-size}
field. Later on I sketch what I believe is the real meaning of the
cost function.

  The following sections discuss functionality that does not depent on
\emph{parameters to codes}.  We will be passing them as Agda module
parameters. The first diffing technique we discuss is the trivial
diff. It's module is declared as follows:

\Agda{RegDiff/Diff/Trivial/Base}{Trivial-module-decl}

  We stick to this nomenclature throughtout the code. The first line
handles constant types: \textit{ks\#} is how many constant types we
have, $ks$ is the vector of such types and $keqs$ is an indexed vector
with a proof of decidable equality over such types. The second line
handles parameters: \textit{parms\#} is how many type-variables our
codes will have, $A$ is the valuation we are using and $WBA$ is a
proof that $A$ is \emph{well behaved}.

  We then declare the following synonyms:

\Agda{RegDiff/Diff/Trivial/Base}{Trivial-defs}

\section{Computing and Representing Patches}

  Intuitively, a \textit{Patch} is some description of a
transformation. Setting the stage, let $A$ and $B$ be a types, $x : A$
and $y : B$ elements of such types.  A \emph{patch} between $x$ and
$y$ can be seen as it's ``application'' (partial) function. That is, a
relation $e \subseteq A \times B$ such that $img\;e\subseteq id$ ($e$
is functional).

   Now, let us discuss some code and build some intuition for what is
what in the above schema.

\subsection{Trivial Diff}

   The simplest possible way to describe a transformation is to say
what is the source and what is the destination of such
transformation. This can be acomplished by the Diagonal functor just
fine.

\Agda{RegDiff/Diff/Trivial/Base}{delta-def}

  Now, take an element $(x , y) : \F{$\Delta$}\;ty\;tv$. The ``apply''
relation it defines is trivial: $ \{ (x , y) \} $, or, in PF style:

\begin{displaymath}
\xymatrix{
  \Interp{ty}{A} \ar@@/^2.0pc/[rr]^{\underline{y} \cdot \underline{x}^\circ} 
  & K \ar[l]^{\underline{x}} \ar[r]_{\underline{y}} & \Interp{tv}{A} 
}
\end{displaymath}

  Where, for any $A , B \in Set$ and $x : A$, $\underline{x} \subseteq A \times B$ 
represents the \emph{everywhere} $x$ relation, defined by
\[
 \underline{x} = \{ (x , b) \mid b \in B \}
\]

  This is a horrible patch however: We can't calculate with it because
we don't know \emph{anything} about \emph{how} $x$ changed indo $y$.

\subsection{Spines}

  We can try to make it better by identifying the longest prefix of
constructors where $x$ and $y$ agree, before giving up and using \F{$\Delta$}. 
Moreover, this becomes much easier if $x$ and $y$ actually have the same type.
In practice, we are only interested in diffing elements of the same language.
It does not make sense to diff a C source file against a Haskell source file.

Nevertheless, we define an \F{S} structure to capture the longest common prefix
of $x$ and $y$:

\Agda{RegDiff/Diff/Regular/Base}{S-def}

Note that \F{S} makes a functor (actually, a free monad!) on
$P$. Computing a spine is easy, first we check whether or not $x$ and
$y$ are equal. If they are, we are done. If not, we inspect the first
constructor and traverse it. Then we repeat.

\Agda{RegDiff/Diff/Regular/Base}{spine-def}

The ``apply'' relations specified by a spine $s$, denoted $s^\flat$ are:

\begin{align*}
  \IC{Scp}^\flat                    &= \hspace{2.3em} \xymatrix{ A & A \ar[l]_{id}} \\
  (\IC{S$\otimes$}\;s_1\;s_2)^\flat &= \xymatrix{ A \times B & A \times B \ar[l]_(.45){s_1^\flat \times s_2^\flat}} \\
  (\IC{Si1}\;s)^\flat               &= \xymatrix{ A + B & A + B \ar[l]_(.45){i_1 \cdot s^\flat \cdot i_1^\circ}} \\                                                   
  (\IC{Si2}\;s)^\flat               &= \xymatrix{ A + B & A + B \ar[l]_(.45){i_2 \cdot s^\flat \cdot i_2^\circ}} \\    
  (\IC{SX}\;(x , y))^\flat          &= \hspace{2.3em} \xymatrix{ A & A \ar[l]_{\underline{y} \cdot \underline{x}^\circ} }
\end{align*}

This has some problems that I do not like. Namelly:
\begin{itemize}
  \item Non-cannonicity: $\IC{Scp}^\flat \equiv (\IC{S$\otimes$}\;\IC{Scp}\;\IC{Scp})^\flat$
        Even though the \F{spine-cp} function will never find the right-hand above, 
        it feels sub-optimal to allow this.

        One possible solution could be to remove \IC{Scp} and handle them through
        the maybe monad. Instead of (\F{S}\;\F{$\Delta$}) we would have (\F{S}\;(\F{Maybe}\;\F{$\Delta$})),
        where the \IC{nothing}s represent copy. This ensures that we can only copy on the leaves.
        Branch \texttt{explicit-cpy} of the repo has this experiment going. It is easier said
        than done.
\end{itemize}

Ignoring the problems and moving forward; note that for any $x$ and
$y$, a spine $s = \F{spine-cp}\;x\;y$ will NEVER contain a product nor
a unit on a leaf (we force going through products and copying units).
Hence, whenever we are traversing $s$ and find a $\IC{SX}$, we know
that: (1) the values of the pair are different and (2) we must be at a
coproduct, a constant type or a type variable. The constant type or
the type variable are out of our control. But we can refine our
\emph{description} in case we arrive at a coproduct.

\subsection{Coproduct Changes}

%format i1 = "\IC{i1}"
%format i2 = "\IC{i2}"
  Let's imagine we are diffing the following values of a type $\mathbbm{1} + (\mathbbm{N}^2 + \mathbbm{N})\times \mathbbm{N}$:
\begin{align*}
  s & = \F{spine-cp}\;(|i2 (i1 (4 , 10) , 5)|)\;(|i2 (i2 10 , 5)|) \\
    & = \IC{Si2}\; (\IC{S$\otimes$}\; (\IC{SX}\; (|i1 (4 , 10)| , |i2 10|))\; \IC{Scp})
\end{align*}

  And now, we want to \F{S-map} over $s$ and refine the \F{$\Delta$} inside to another type, that contains information
about which injections we need to pattern match on and which we need to introduce.
One step at a time, though. Let's first look how could we represent this information:

We begin with a type (that's also a free monad) that encodes the injections we need to insert on the \emph{destination}:

\Agda{RegDiff/Diff/Regular/Base}{C-def}

And we make an eager function that will consume ALL injections from the right:

\Agda{RegDiff/Diff/Regular/Base}{change-def}

Now, we could \F{S-map} \F{change} over $s$:

\begin{align*}
  \F{S-map}\; \F{change} \; s 
    & = \IC{Si2}\; (\IC{S$\otimes$}\; (\IC{SX}\; (\IC{Ci2}\;(\IC{CX}\;(|i1 (4 , 10)| , 10))))\; \IC{Scp}) \\
    &= s'
\end{align*}

But we are still left with that \IC{i1} on the left\footnote{%
Previously, we had a \emph{flip} constructor inside our datatype that
would let we flip arguments anytime, at will. This is far from ideal,
however. In fact, it was this internal \emph{flip} that was causing
the first algorithm to not terminate for fixpoints.}.
Well, this is easy if we could only flip the arguments to \F{C}:

\Agda{RegDiff/Diff/Regular/Base}{Sym-def}

And now, we can \F{C-map} \F{change} with its arguments flipped over the previous $s'$:
\begin{align*}
  \F{C-map}\; (\F{flip change}) \; s'
    & = \IC{Si2}\; (\IC{S$\otimes$}\; (\IC{SX}\; (\IC{Ci2}\;(\IC{CX}\;(\IC{Ci1} \; (10, (4 , 10))))\; \IC{Scp})
\end{align*}

And bingo! We now have the largest common prefix and information about the differing coproducts on the leaves
of this prefix. The whole thing also becomes of a much more expressive type:

\begin{align*}
  \F{C-map}\; (\F{flip change}) \; (\F{S-map}\; \F{change} \; s) &: \F{S}\;(\F{C}\;(\F{Sym}\;(\F{C}\;\F{$\Delta$})))
\end{align*}

We can read the type as: a common prefix from both terms followed by injections into the target term followed
by pattern matching on the source term followed by pointwise changes. 

Just like the values of \F{S}, we can also define the ``apply'' relation induced by the values of \F{C} and \F{Sym}.
They are trivial, however. \F{C} induces composition with injections, \F{Sym} induces converses (which is the relational
way of flipping things around).

Note that up until now, everything was deterministic! This is something we are about to lose.

\subsection{Aligning Everything}

Following a similar reasoning as from \F{S} to \F{C}; the leaves of a \F{C} produced through
\F{change} will NEVER contain a coproduct injection. Hence, we know that they will contain
either a product, or a constant type, or a type variable. In the case of a constant type
or a type variable, there is not much we can do at the moment, but for a product we can 
refine this a little bit more before using \F{$\Delta$}.

In fact, splitting different stages of the algorithm into different types reinforced
our intuition that the alignment is the source of difficulties. As we shall see, we now need
to introduce non-determinism. 

\section{Conclusion}
  
\end{document}


That is, the general template we are looking for is:

%format (Interp x) = "\llbracket{" x "}\rrbracket"
\begin{code}
Patch   : U -> Set

diff    : {ty : U}(x y : (Interp ty)) -> Patch ty

apply   : {ty : U} -> Patch ty -> (Interp ty) -> Maybe (Interp ty)
\end{code}