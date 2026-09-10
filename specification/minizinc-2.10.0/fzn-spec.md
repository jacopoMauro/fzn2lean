<!DOCTYPE html> 

* [](https://docs.minizinc.dev/en/2.10.0/index.html)
* [4\. Reference Manual](https://docs.minizinc.dev/en/2.10.0/part%5F4%5Freference.html)
* 4.3\. Interfacing Solvers to Flatzinc

---

# 4.3\. Interfacing Solvers to Flatzinc[](#interfacing-solvers-to-flatzinc "Link to this heading")

This document describes the interface between the MiniZinc system and FlatZinc solvers. Interfacing a solver with MiniZinc usually requires three components:

1. The solver binary (or a script that runs the solver). It should support the command line options specified in [Section 4.3.5](#fzn-cmdline-options), understand either the FlatZinc input language as defined in [Section 4.3.1](#ch-fzn-spec), or the FlatZinc-JSON input language as defined in [Section 4.3.2](#ch-fzn-json). Solvers must produce output as defined in [Section 4.3.3](#ch-fzn-output).
2. The solver’s MiniZinc library. This library defines the global constraints that the solver supports, and redefines FlatZinc built-in constraints that the solver does not support (see [Section 4.3.4](#ch-solver-specific-libraries)).
3. The solver’s configuration file. This file makes the solver known to the minizinc driver program and the MiniZinc IDE. Configuration files are discussed in [Section 4.3.6](#sec-cmdline-conffiles).

We recommend to install solvers following something similar to the Linux Filesystem Hierarchy Standard: When installing a solver called $SOLVERNAME in a directory $PREFIX, its binary should be put in $PREFIX/bin, its MiniZinc library files should be in $PREFIX/share/minizinc/$SOLVERNAME/, and its solver configuration file should be $PREFIX/share/minizinc/solvers/$SOLVERNAME.mzc. The prefix can either be a global installation path (such as /usr/local) or any other path.

## 4.3.1\. Specification of FlatZinc[](#specification-of-flatzinc "Link to this heading")

FlatZinc is the target constraint modelling language into which MiniZinc models are translated. It is a very simple solver independent problem specification language, requiring minimal implementation effort to support.

Throughout this document: \\(r\_1\\), \\(r\_2\\) denote float literals; \\(x\_1, x\_2, \\dots, x\_k, i, j, k\\) denote int literals; \\(y\_1, y\_2, \\dots, y\_k, y\_i\\) denote literal array elements.

### 4.3.1.1\. Comments[](#comments "Link to this heading")

Comments start with a percent sign % and extend to the end of the line. Comments can appear anywhere in a model.

### 4.3.1.2\. Types[](#types "Link to this heading")

There are three varieties of types in FlatZinc.

* _Parameter_ types apply to fixed values that are specified directly in the model.
* _Variable_ types apply to values computed by the solver during search. Every parameter type has a corresponding variable type; the variable type being distinguished by a var keyword.
* _Annotations_ and _strings_: annotations can appear on variable declarations, constraints, and on the solve goal. They provide information about how a variable or constraint should be treated by the solver (e.g., whether a variable should be output as part of the result or whether a particular constraint should implemented using domain consistency). Strings may appear as arguments to annotations, but nowhere else.

#### Parameter types[](#parameter-types "Link to this heading")

Parameters are fixed quantities explicitly specified in the model (see rule `<par-type>` in [Section 4.3.7](#ch-fzn-syntax)).

| Type                                 | Values                |
| ------------------------------------ | --------------------- |
| bool                                 | true or false         |
| float                                | float                 |
| int                                  | int                   |
| set of int                           | subset of int         |
| array \[1.. \\(n\\) \] of bool       | array of bools        |
| array \[1.. \\(n\\) \] of float      | array of floats       |
| array \[1.. \\(n\\) \] of int        | array of ints         |
| array \[1.. \\(n\\) \] of set of int | array of sets of ints |

A parameter may be used where a variable is expected, but not vice versa.

In predicate declarations the following additional parameter types are allowed.

| Type                                                                 | Values                         |
| -------------------------------------------------------------------- | ------------------------------ |
| \\(r\_a\\) .. \\(r\_b\\)                                             | bounded float                  |
| \\(x\_a\\) .. \\(x\_b\\)                                             | int in range                   |
| { \\(x\_a, x\_b, \\ldots, x\_k\\) }                                  | int in set                     |
| set of \\(x\_a\\) .. \\(x\_b\\)                                      | subset of int range            |
| set of { \\(x\_a, x\_b, \\ldots, x\_k\\) }                           | subset of int set              |
| array \[1.. \\(n\\) \] of \\(r\_a\\) .. \\(r\_b\\)                   | array of floats in range       |
| array \[1.. \\(n\\) \] of \\(x\_a\\) .. \\(x\_b\\)                   | array of ints in range         |
| array \[1.. \\(n\\) \] of set of \\(x\_a\\) .. \\(x\_b\\)            | array of sets of ints in range |
| array \[1.. \\(n\\) \] of set of { \\(x\_a, x\_b, \\ldots, x\_k\\) } | array of subsets of set        |

A range \\(x\_a\\) .. \\(x\_b\\) denotes a closed interval \\(\\{x | x\_a \\leq x \\leq x\_b\\}\\) (same for float ranges).

An array type appearing in a predicate declaration may use just int instead of 1.. \\(n\\) for the array index range in cases where the array argument can be of any length.

#### Variable types[](#variable-types "Link to this heading")

Variables are quantities decided by the solver (see rules `<basic-var-type>` and `<array-var-type>` in [Section 4.3.7](#ch-fzn-syntax)).

| Variable type                                                            |
| ------------------------------------------------------------------------ |
| var bool                                                                 |
| var float                                                                |
| var \\(r\_a\\) .. \\(r\_b\\)                                             |
| var int                                                                  |
| var \\(x\_a\\) .. \\(x\_b\\)                                             |
| var { \\(x\_a, x\_b, \\ldots, x\_k\\) }                                  |
| var set of \\(x\_a\\) .. \\(x\_b\\)                                      |
| var set of { \\(x\_a, x\_b, \\ldots, x\_k\\) }                           |
| array \[1.. \\(n\\) \] of var bool                                       |
| array \[1.. \\(n\\) \] of var float                                      |
| array \[1.. \\(n\\) \] of var \\(r\_a\\) .. \\(r\_b\\)                   |
| array \[1.. \\(n\\) \] of var int                                        |
| array \[1.. \\(n\\) \] of var \\(x\_a\\) .. \\(x\_b\\)                   |
| array \[1.. \\(n\\) \] of var set of \\(x\_a\\) .. \\(x\_b\\)            |
| array \[1.. \\(n\\) \] of var set of { \\(x\_a, x\_b, \\ldots, x\_k\\) } |

In predicate declarations the following additional variable types are allowed.

| Variable type                            |
| ---------------------------------------- |
| var set of int                           |
| array \[1.. \\(n\\) \] of var set of int |

An array type appearing in a predicate declaration may use just int instead of 1.. \\(n\\) for the array index range in cases where the array argument can be of any length.

#### The string type[](#the-string-type "Link to this heading")

String literals and literal arrays of string literals can appear as annotation arguments, but not elsewhere. Strings have the same syntax as in C programs (namely, they are delimited by double quotes and the backslash character is used for escape sequences).

Examples:

""                              % The empty string.
"Hello."
"Hello,\nWorld\t\"quoted!\""    % A string with an embedded newline, tab and quotes.

### 4.3.1.3\. Values and expressions[](#values-and-expressions "Link to this heading")

(See rule `<expr>` in [Section 4.3.7](#ch-fzn-syntax))

Examples of literal values:

Type Literals bool true, false float 2.718, \-1.0, 3.0e8 int \-42, 0, 69 set of int {}, {2, 3, 5}, 1..10 arrays \[\], \[ \\(y\_a, \\ldots, y\_k\\) \]

where each array element \\(y\_i\\) is either: a non-array literal, or the name of a non-array parameter or variable, v. For example:

[1, 2, 3]             % Just literals
[x, y, z]             % x, y, and z are variables or parameters.
[x, 3]                % Mix of identifiers and literals

[Section 4.3.7](#ch-fzn-syntax) gives the regular expressions specifying the syntax for float and int literals.

### 4.3.1.4\. FlatZinc models[](#flatzinc-models "Link to this heading")

A FlatZinc model consists of:

1. zero or more external predicate declarations (i.e., a non-standard predicate that is supported directly by the target solver);
2. zero or more parameter declarations;
3. zero or more variable declarations;
4. zero or more constraints;
5. a solve goal

in that order.

FlatZinc uses the UTF-8 character set. Non-ASCII characters can only appear in string literals.

FlatZinc syntax is case sensitive (foo and Foo are different names). Identifiers start with a letter (\[A-Za-z\]) and are followed by any sequence of letters, digits, or underscores (\[A-Za-z0-9\_\]). Additionally, identifiers of variable or parameter names may start with an underscore. Identifiers that correspond to the names of predicates, predicate parameters and annotations cannot have leading underscores.

The following keywords are reserved and cannot be used as identifiers: annotation, any, array, bool, case, constraint, diff, div, else, elseif, endif, enum, false, float, function, if, in, include, int, intersect, let, list, maximize, minimize, mod, not, of, satisfy, subset, superset, output, par, predicate, record, set, solve, string, symdiff, test, then, true, tuple, union, type, var, where, xor. Note that some of these keywords are not used in FlatZinc. They are reserved because they are keywords in Zinc and MiniZinc.

FlatZinc syntax is insensitive to whitespace.

### 4.3.1.5\. Predicate declarations[](#predicate-declarations "Link to this heading")

(See rule `<predicate-item>` in [Section 4.3.7](#ch-fzn-syntax))

Predicates used in the model that are not standard FlatZinc must be declared at the top of a FlatZinc model, before any other lexical items. Predicate declarations take the form

<predicate-item> ::= "predicate" <identifier> "(" [ <pred-param-type> ":" <identifier> "," ... ] ")" ";"

Annotations are not permitted anywhere in predicate declarations.

It is illegal to supply more than one predicate declaration for a given `<identifier>`.

Examples:

    % m is the median value of {x, y, z}.
    %
predicate median_of_3(var int: x, var int: y, var int: z, var int: m);

    % all_different([x1, .., xn]) iff
    % for all i, j in 1..n: xi != xj.
    %
predicate all_different(array [int] of var int: xs);

    % exactly_one([x1, .., xn]) iff
    % there exists an i in 1..n: xi = true
    % and for all j in 1..n: j != i -> xj = false.
    %
predicate exactly_one(array [int] of var bool: xs);

### 4.3.1.6\. Parameter declarations[](#parameter-declarations "Link to this heading")

(See rule param\_decl in [Section 4.3.7](#ch-fzn-syntax))

Parameters have fixed values and must be assigned values:

<par-decl-item> ::= "array" "[" <index-set> "]" "of" <basic-par-type> ":" <var-par-identifier> "=" <par-array-literal> ";"

where `<par-type>` is a parameter type, `<var-par-identifier>` is an identifier, and `<par-expr>` is a literal value (either a basic integer, float or bool literal, or a set or array of such literals).

Annotations are not permitted anywhere in parameter declarations.

Examples:

float: pi = 3.141;
array [1..7] of int: fib = [1, 1, 2, 3, 5, 8, 13];
bool: beer_is_good = true;

### 4.3.1.7\. Variable declarations[](#variable-declarations "Link to this heading")

(See rule var\_decl in [Section 4.3.7](#ch-fzn-syntax))

Variables have variable types and can be declared with optional assignments. The assignment can fix a variable to a literal value, or create an alias to another variable. Arrays of variables always have an assignment, defining them in terms of an array literal that can contain identifiers of variables or constant literals. Variables may be declared with zero or more annotations.

<var-decl-item> ::= <basic-var-type> ":" <var-par-identifier> <annotations> [ "=" <basic-expr> ] ";"
                  | <array-var-type> ":" <var-par-identifier> <annotations> "=" <array-literal> ";"

where `<basic-var-type>` and `<array-var-type>` are variable types, `<var-par-identifier>` is an identifier, `<annotations>` is a (possibly empty) set of annotations, `<basic-expr>` is an identifier or a literal, and `<array-literal>` is a literal array value.

Examples:

var 0..9: digit;
var bool: b;
var set of 1..3: s;
var 0.0..1.0: x;
var int: y :: mip;        % 'mip' annotation: y should be a MIP variable.
array [1..3] of var 1..10: b = [y, 3, digit];

### 4.3.1.8\. Constraints[](#constraints "Link to this heading")

(See rule `<constraint-item>` in [Section 4.3.7](#ch-fzn-syntax))

Constraints take the following form and may include zero or more annotations:

<constraint-item> ::= "constraint" <identifier> "(" [ <expr> "," ... ] ")" <annotations> ";"

The arguments expressions (`<expr>`) can be literal values or identifiers.

Examples:

constraint int_le(0, x);    % 0 <= x
constraint int_lt(x, y);    % x <  y
constraint int_le(y, 10);   % y <= 10
    % 'domain_propagation': use domain consistency for this constraint:
    % 2x + 3y = 10
constraint int_lin_eq([2, 3], [x, y], 10) :: domain_propagation;

### 4.3.1.9\. Solve item[](#solve-item "Link to this heading")

(See rule `<solve-item>` in [Section 4.3.7](#ch-fzn-syntax))

A model finishes with a solve item, taking one of the following forms:

<solve-item> ::= "solve" <annotations> "satisfy" ";"
               | "solve" <annotations> "minimize" <basic-expr> ";"
               | "solve" <annotations> "maximize" <basic-expr> ";"

The first alternative searches for any satisfying assignment, the second one searches for an assignment minimizing the given expression, and the third one for an assignment maximizing the expression. The `<basic-expr>` can be either a variable identifier or a literal value (if the objective function is constant).

A solution consists of a complete assignment where all variables in the model have been given a fixed value.

Examples:

solve satisfy;      % Find any solution using the default strategy.

solve minimize w;   % Find a solution minimizing w, using the default strategy.

    % First label the variables in xs in the order x[1], x[2], ...
    % trying values in ascending order.
solve :: int_search(xs, input_order, indomain_min, complete)
    satisfy;    % Find any solution.

    % First use first-fail on these variables, splitting domains
    % at each choice point.
solve :: int_search([x, y, z], first_fail, indomain_split, complete)
    maximize x; % Find a solution maximizing x.

### 4.3.1.10\. Annotations[](#annotations "Link to this heading")

Annotations are optional suggestions to the solver concerning how individual variables and constraints should be handled (e.g., a particular solver may have multiple representations for int variables) and how search should proceed. An implementation is free to ignore any annotations it does not recognise, although it should print a warning on the standard error stream if it does so. Annotations are unordered and idempotent: annotations can be reordered and duplicates can be removed without changing the meaning of the annotations.

An annotation is prefixed by ::, and either just an identifier or an expression that looks like a predicate call:

<annotations> ::= [ "::" <annotation> ]*

<annotation> ::= <identifier>
               | <identifier> "(" <ann-expr> "," ... ")"

<ann-expr>   := <basic-ann-expr>
              | "[" [ <basic-ann-expr> "," ... ] "]"

<basic-ann-expr>   := <basic-literal-expr>
                    | <var-par-identifier>
                    | <string-literal>
                    | <annotation>

<string-contents> ::= ([^"\n\] | \[^\n(])*

<string-literal> ::= """ <string-contents> """

The arguments of the second alternative can be any expression or other annotations (without the leading ::).

#### Search annotations[](#search-annotations "Link to this heading")

While an implementation is free to ignore any or all annotations in a model, it is recommended that implementations at least recognise the following standard annotations for solve items.

seq_search([<searchannotation>, ...])

allows more than one search annotation to be specified in a particular order (otherwise annotations can be handled in any order).

A `<searchannotation>` is one of the following:

int_search(<vars>, <varchoiceannotation>, <assignmentannotation>, <strategyannotation>)

bool_search(<vars>, <varchoiceannotation>, <assignmentannotation>, <strategyannotation>)

set_search(<vars>, <varchoiceannotation>, <assignmentannotation>, <strategyannotation>)

where `<vars>` is the identifier of an array variable or an array literal specifying the variables to be assigned (ints, bools, or sets respectively). Note that these arrays may contain literal values.

`<varchoiceannotation>` specifies how the next variable to be assigned is chosen at each choice point. Possible choices are as follows (it is recommended that implementations support the starred options):

| input\_order      | \\(\\star\\) | Choose variables in the order they appear in vars.                                                                                                                                      |
| ----------------- | ------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| first\_fail       | \\(\\star\\) | Choose the variable with the smallest domain.                                                                                                                                           |
| anti\_first\_fail |              | Choose the variable with the largest domain.                                                                                                                                            |
| smallest          |              | Choose the variable with the smallest value in its domain.                                                                                                                              |
| largest           |              | Choose the variable with the largest value in its domain.                                                                                                                               |
| occurrence        |              | Choose the variable with the largest number of attached constraints.                                                                                                                    |
| most\_constrained |              | Choose the variable with the smallest domain, breaking ties using the number of constraints.                                                                                            |
| max\_regret       |              | Choose the variable with the largest difference between the two smallest values in its domain.                                                                                          |
| dom\_w\_deg       |              | Choose the variable with the smallest value of domain size divided by weighted degree, where the weighted degree is the number of times the variables been in a constraint which failed |

`<assignmentannotation>` specifies how the chosen variable should be constrained. Possible choices are as follows (it is recommended that implementations support at least the starred options):

| indomain\_min            | \\(\\star\\) | Assign the smallest value in the variable’s domain.                                                                                                     |
| ------------------------ | ------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------- |
| indomain\_max            | \\(\\star\\) | Assign the largest value in the variable’s domain.                                                                                                      |
| indomain\_middle         |              | Assign the value in the variable’s domain closest to the mean of its current bounds.                                                                    |
| indomain\_median         |              | Assign the middle value in the variable’s domain.                                                                                                       |
| indomain                 |              | Nondeterministically assign values to the variable in ascending order.                                                                                  |
| indomain\_random         |              | Assign a random value from the variable’s domain.                                                                                                       |
| indomain\_split          |              | Bisect the variable’s domain, excluding the upper half first.                                                                                           |
| indomain\_reverse\_split |              | Bisect the variable’s domain, excluding the lower half first.                                                                                           |
| indomain\_interval       |              | If the variable’s domain consists of several contiguous intervals, reduce the domain to the first interval. Otherwise just split the variable’s domain. |

Of course, not all assignment strategies make sense for all search annotations (e.g., bool\_search and indomain\_split).

Finally, `<strategyannotation>` specifies a search strategy; implementations should at least support complete (i.e., exhaustive search).

#### Output annotations[](#output-annotations "Link to this heading")

Model output is specified through variable annotations. Non-array output variables are annotated with output\_var. Array output variables are annotated with output\_array(\[ \\(1\\) .. \\(x\\) \`\` \])\`\` where \\(1\\) .. \\(x\\) is the index set range of the array. See [Section 4.3.3](#ch-fzn-output) for details on the output format.

#### Variable definition annotations[](#variable-definition-annotations "Link to this heading")

To support solvers capable of exploiting functional relationships, a variable defined as a function of other variables may be annotated thus:

var int: x :: is_defined_var;

...

constraint int_plus(y, z, x) :: defines_var(x);

(The defines\_var annotation should appear on exactly one constraint.) This allows a solver to represent x internally as a representation of y+z rather than as a separate constrained variable. The is\_defined\_var annotation on the declaration of xprovides “early warning” to the solver that such an option is available.

#### Intermediate variables[](#intermediate-variables "Link to this heading")

Intermediate variables introduced during conversion of a MiniZinc model to FlatZinc may be annotated thus:

var int: X_INTRODUCED_3 :: var_is_introduced;

This information is potentially useful to the solver’s search strategy.

#### Constraint annotations[](#constraint-annotations "Link to this heading")

Annotations can be placed on constraints advising the solver how the constraint should be implemented. Here are some constraint annotations supported by some solvers:

| bounds             | Use bounds propagation. The concrete propagation strength is not furtherspecified. |
| ------------------ | ---------------------------------------------------------------------------------- |
| boundsZ            | Use integer bounds propagation.                                                    |
| boundsR            | Use real bounds propagation.                                                       |
| boundsD            | A tighter version of boundsZ where support for the bounds must exist.              |
| domain             | Use domain propagation.                                                            |
| value\_propagation | Use value propagation.                                                             |
| priority(k)        | where k is an integer constant indicating propagator priority.                     |

## 4.3.2\. Specification of FlatZinc-JSON[](#specification-of-flatzinc-json "Link to this heading")

FlatZinc-JSON is an alternative syntax for FlatZinc that is compatible with the JSON data format. Solvers can indicate that they require FlatZinc output in their solver configuration files (see [Section 4.3.6](#sec-cmdline-conffiles)) using the inputType property.

The JSON representation of FlatZinc contains the same elements as a FlatZinc file: declarations of variables, arrays, constraints and a solve item. A full specification is given as a JSON schema at the end of this section. Here is an example of the cake optimisation model from [Listing 2.1.2](https://docs.minizinc.dev/en/2.10.0/modelling.html#ex-cakes), compiled into FlatZinc-JSON:

{
  "variables": {
    "b" : { "type" : "int", "domain" : [[0, 3]] },
    "c" : { "type" : "int", "domain" : [[0, 6]] },
    "X_INTRODUCED_0_" : { "type" : "int", "domain" : [[0, 85000]], "defined" : true }
  },
  "arrays": {
    "X_INTRODUCED_2_" : { "a": [250, 200] },
    "X_INTRODUCED_6_" : { "a": [75, 150] },
    "X_INTRODUCED_8_" : { "a": [100, 150] }
  },
  "constraints": [
    { "id" : "int_lin_le", "args" : ["X_INTRODUCED_2_", ["b", "c"], 4000]},
    { "id" : "int_lin_le", "args" : ["X_INTRODUCED_6_", ["b", "c"], 2000]},
    { "id" : "int_lin_le", "args" : ["X_INTRODUCED_8_", ["b", "c"], 500]},
    { "id" : "int_lin_eq", "args" : [[400, 450, -1], ["b", "c", "X_INTRODUCED_0_"], 0],
      "ann" : ["ctx_pos"], "defines" : "X_INTRODUCED_0_"}
  ],
  "output": ["b", "c"],
  "solve": { "method" : "maximize", "objective" : "X_INTRODUCED_0_" },
  "version": "1.0"
}

There are a number of small differences compared to FlatZinc:

* Variables and arrays are declared separately. Each variable must have an identifier and a type, and can optionally have a domain, a flag indicating that the variable was introduced by compilation, a flag that the variable is functionally defined by a constraint, and a property "rhs" to define the “right hand side” of the variable, i.e., its value or alias to another variable.
* Domains are written as lists of contiguous, ordered, non-overlapping ranges. E.g., the set `{1,2,4,6,7}` would be written as \[\[1,2\],\[4,4\],\[6,7\]\].
* Arrays are declared with an identifier and an object that has the property "a", which maps to the actual array. Arrays can contain numeric literals or identifiers (written as strings).
* Constraints are declared as objects with a property "id" indicating the name of the constraint, a property "args" for the array of arguments to the constraint, and an optional property "defines" that indicates the variable identifier that this constraint functionally defines.
* The "output" property is a list of all identifiers for which the solver must produce output for each solution. The output must follow the normal FlatZinc output rules as defined in [Section 4.3.3](#ch-fzn-output).
* The "solve" property maps to an object with a property "method" that indicates whether the problem is a satisfaction problem ("satisfy") or an optimisation problem ("minimize" or "maximize"), in which case the "objective" property must be present, which maps to an identifier.
* Variables, arrays, constraints and the solve item can have an optional list of annotations, indicated by the "ann" property. Atomic annotations (such as indomain\_min) are represented simply as strings. Non-atomic annotations (such as int\_search) follow the same syntax as constraints, i.e., an object with "id" and "args" properties.
String literals can occur in FlatZinc as arguments to annotations or special solver-defined predicates. In FlatZinc-JSON, these string literals are represented as objects { "string" : "" }. 

The full schema is listed below, and is available from <https://www.minizinc.org/schemas/fznjson>.

{
  "$schema": "http://json-schema.org/draft-04/schema#",
  "$id": "https://www.minizinc.org/schemas/fznjson",
  "title" : "FlatZincJSON",
  "description" : "A JSON representation of a FlatZinc model",

  "$defs" : {
    "identifier" : { "type" : "string", "pattern" : "[A-Za-z][A-Za-z0-9_]*" },
    "literal" : { "oneOf" : [
      { "type" : "number" },
      { "$ref" : "#/$defs/identifier" },
      { "type" : "boolean" },
      { "type" : "object",
        "properties" : {
          "set" : {
            "type" : "array",
            "items" : {
                        "type" : "array",
                        "items" : [
                          { "type" : "number" },
                          { "type" : "number" }
                        ]        
                       }
          }
        },
        "required" : [ "set" ]
      },
      { "type" : "object",
        "properties" : {
          "string" : { "type" : "string" }
        },
        "required" : [ "string" ]
      }
    ]},
    "literals" : { "type" : "array", "items" : { "$ref" : "#/$defs/literal" } },
    "argument" : { "oneOf" : [
      { "$ref" : "#/$defs/literals"},
      { "$ref" : "#/$defs/literal" }
    ]},
    "annotation" : { "oneOf" : [
      { "$ref" : "#/$defs/annotationCall" },
      { "type" : "string" }
    ]},
    "annotations" : {
      "type" : "array",
      "items" : { "$ref" : "#/$defs/annotation" }
    },
    "annotationArgument" : { "oneOf" : [
      { "$ref" : "#/$defs/annotationLiterals"},
      { "$ref" : "#/$defs/annotationLiteral" }
    ]},
    "annotationCall" : {
      "type" : "object",
      "properties" : {
        "id": { "$ref": "#/$defs/identifier" },
        "args": {
          "type": "array",
          "items": { "$ref" : "#/$defs/annotationArgument" }
        }
      },
      "required": [
        "id",
        "args"
      ]
    },
    "annotationLiterals" : { "type" : "array", "items" : { "$ref" : "#/$defs/annotationLiteral" } },
    "annotationLiteral" : { "oneOf" : [
      { "$ref" : "#/$defs/literal"},
      { "$ref" : "#/$defs/annotationCall" }
    ]},
    "domain" : {
      "type" : "array",
      "items" : {
        "type" : "array",
        "items" : [
          { "type" : "number" },
          { "type" : "number" }
        ]
      }
    }
  },

  "type": "object",
  "properties": {
    "version" : { "type" : "string" },
    "variables": {
      "type": "object",
      "patternProperties": {
        "[A-Za-z][A-Za-z0-9_]*": {
          "type": "object",
          "properties": {
            "type": {
              "enum": [
                "bool",
                "float",
                "int",
                "set of int"
               ]
            },
            "domain": { "$ref" : "#/$defs/domain" },
            "introduced": {
              "type": "boolean"
            },
            "defined": {
              "type": "boolean"
            },
            "ann" : { "$ref" : "#/$defs/annotations"}
          },
          "required": [
            "type"
          ]
        }
      }
    },
    "arrays": {
      "type": "object",
      "patternProperties": {
        "[A-Za-z][A-Za-z0-9_]*": {
          "type": "object",
          "properties": {
            "a": {
              "type": "array",
              "items": { "$ref" : "#/$defs/literal" }
            },
            "ann" : { "$ref" : "#/$defs/annotations"},
            "introduced": {
              "type": "boolean"
            },
            "defined": {
              "type": "boolean"
            }
          },
          "required": [
            "a"
          ]
        }
      }
    },
    "constraints": {
      "type": "array",
      "items": {
        "type" : "object",
        "properties" : {
          "id": { "$ref": "#/$defs/identifier" },
          "args": {
            "type": "array",
            "items": { "$ref" : "#/$defs/argument" }
          },
          "ann" : { "$ref" : "#/$defs/annotations"},
          "defines": { "$ref": "#/$defs/identifier" }
        },
        "required": [
          "id",
          "args"
        ]
      }
    },
    "output": {
      "type": "array",
      "items": { "$ref" : "#/$defs/identifier" }
    },
    "solve": {
      "type": "object",
      "properties": {
        "method": {
          "enum": [ "satisfy", "minimize", "maximize" ]
        },
        "objective": { "$ref" : "#/$defs/literal" },
        "ann" : { "$ref" : "#/$defs/annotations"}
    },
      "required": [
        "method"
      ]
    }
  },
  "required": [
    "version",
    "variables",
    "arrays",
    "output",
    "constraints",
    "solve"
  ]
}

## 4.3.3\. Output[](#output "Link to this heading")

An implementation can produce three types of output: solutions, statistics, and errors.

### 4.3.3.1\. Solution output[](#solution-output "Link to this heading")

An implementation must output values for all and only the variables annotated with output\_var or output\_array (output annotations must not appear on parameters) in a FlatZinc model, or those variables and arrays whose identifiers are listed in the "output" property of a FlatZinc-JSON model. Output must be printed to the standard output stream.

For example:

var 1..10: x :: output_var;
var 1..10: y;       % y is not output.
array [1..4] of var int: zs :: output_array([1..4]);

All non-error output must be sent to the standard output stream.

Output must take the following form:

<var-par-identifier> = <basic-literal-expr> ;

or, for array variables,

<var-par-identifier> = [<y1>, <y2>, ... <yk>];

where `<y1>, <y2>, ... <yk>` are literals of the element type.

**Note**: The argument to the `output_array` annotation is kept for compatibility with older versions of FlatZinc. Previous versions of the MiniZinc compiler generated multi-dimensional `output_array` annotations, and required the solver to output corresponding `arrayNd` calls (with `N` being the number of dimensions). Starting from MiniZinc version 2.7.8, all `output_array` annotations are guaranteed to be one-dimensional and 1-based, so that no `arrayNd` calls are required.

Using this format, the output of a FlatZinc model solution is suitable for input to a MiniZinc model as a data file (this is why parameters are not included in the output).

Implementations must ensure that _all_ model variables (not just the output variables) have satisfying assignments before printing a solution.

The output for a solution must be terminated with ten consecutive minus signs on a separate line: \----------.

Multiple solutions may be output, one after the other, as search proceeds. How many solutions should be output depends on the mode the solver is run in as controlled by the \-a command line flag (see [Section 4.3.5](#fzn-cmdline-options)).

If at least one solution has been found and search then terminates having explored the whole search space, then ten consecutive equals signs should be printed on a separate line: \==========.

If no solutions have been found and search terminates having explored the whole search space, then \=====UNSATISFIABLE===== should be printed on a separate line.

If the objective of an optimization problem is unbounded, then \=====UNBOUNDED===== should be printed on a separate line.

If no solutions have been found and search terminates having _not_ explored the whole search space, then \=====UNKNOWN===== should be printed on a separate line.

Implementations may output further information about the solution(s), or lack thereof, in the form of FlatZinc comments.

Examples:

Asking for a single solution to this model:

var 1..3: x :: output_var;
solve satisfy

might produce this output:

x = 1;
----------

Asking for all solutions to this model:

array [1..2] of var 1..3: xs :: output_array([1..2]);
constraint int_lt(xs[1], xs[2]);    % x[1] < x[2].
solve satisfy

might produce this output:

xs = array1d(1..2, [1, 2]);
----------
xs = array1d(1..2, [1, 3]);
----------
xs = array1d(1..2, [2, 3]);
----------
==========

Asking for a single solution to this model:

var 1..10: x :: output_var;
solve maximize x;

should produce this output:

x = 10;
----------
==========

The row of equals signs indicates that a complete search was performed and that the last result printed is the optimal solution.

Running a solver on this model with some termination condition (such as a very short time-out):

var 1..10: x :: output_var;
solve maximize x;

might produce this output:

x = 1;
----------
x = 2;
----------
x = 3;
----------

Because the output does not finish with \==========, search did not finish, hence these results must be interpreted as approximate solutions to the optimization problem.

Asking for a solution to this model:

var 1..3: x :: output_var;
var 4..6: y :: output_var;
constraint int_lt(y, x);    % y < x.
solve satisfy;

should produce this output:

=====UNSATISFIABLE=====

indicating that a complete search was performed and no solutions were found (i.e., the problem is unsatisfiable).

### 4.3.3.2\. Statistics output[](#statistics-output "Link to this heading")

FlatZinc solvers can output statistics in a standard format so that it can be read by scripts, for example, in order to run experiments and automatically aggregate the results. Statistics should be printed to the standard output stream in the form of FlatZinc comments that follow a specific format. Statistics can be output at any time during the solving, i.e., before the first solution, between solutions, and after the search has finished. Statistics output corresponding to a solution should be the last one before its ‘———-’ separator.

Each value should be output on a line of its own in the following format:

%%%mzn-stat: <name>=<value>

Each block of statistics is terminated by a line of its own with the following format:

%%%mzn-stat-end

**Example**

%%%mzn-stat: objective=1e+308
%%%mzn-stat: objectiveBound=0
%%%mzn-stat: nodes=0
%%%mzn-stat: solveTime=2.3567
%%%mzn-stat-end

(no feasible solution found yet but something can be printed...)

%%%mzn-stat: objective=12345
%%%mzn-stat: objectiveBound=122
%%%mzn-stat: nodes=35
%%%mzn-stat: solveTime=78.5799
%%%mzn-stat-end

(the corresponding feasible solution with value 12345 goes here
   or before its statistics but above the separator)
----------               (<- the solution separator)

%%%mzn-stat: objective=379
%%%mzn-stat: objectiveBound=379
%%%mzn-stat: nodes=4725
%%%mzn-stat: solveTime=178.5799
%%%mzn-stat-end

(the corr. optimal solution with value 379 goes here)
----------
==========               (<- the 'search complete' marker)

%%%mzn-stat: objective=379      (<- this is the concluding output)
%%%mzn-stat: objectiveBound=379
%%%mzn-stat: nodes=13456
%%%mzn-stat: solveTime=2378.5799
%%%mzn-stat-end

The `<name>` describes the kind of statistics gathered, and the `<value>` can be any value of a MiniZinc type. The following names are considered standard statistics:

| Name           | Type  | Explanation                                     |
| -------------- | ----- | ----------------------------------------------- |
| nodes          | int   | Number of search nodes                          |
| openNodes      | int   | Number of open search nodes                     |
| objective      | float | Current objective value                         |
| objectiveBound | float | Dual bound on the objective value               |
| failures       | int   | Number of leaf nodes that were failed           |
| restarts       | int   | Number of times the solver restarted the search |
| variables      | int   | Number of variables                             |
| intVariables   | int   | Number of integer variables created             |
| boolVariables  | int   | Number of bool variables created                |
| floatVariables | int   | Number of float variables created               |
| setVariables   | int   | Number of set variables created                 |
| propagators    | int   | Number of propagators created                   |
| propagations   | int   | Number of propagator invocations                |
| peakDepth      | int   | Peak depth of search tree                       |
| nogoods        | int   | Number of nogoods created                       |
| backjumps      | int   | Number of backjumps                             |
| peakMem        | float | Peak memory (in Mbytes)                         |
| initTime       | float | Initialisation time (in seconds)                |
| solveTime      | float | Solving time (in seconds)                       |

### 4.3.3.3\. Unsatisfiable core output (experimental)[](#unsatisfiable-core-output-experimental "Link to this heading")

Note

Unsatisfiable core output is part of the **experimental** assumption interface (see [Section 3.7](https://docs.minizinc.dev/en/2.10.0/assumptions.html#ch-assumptions)) and may change in future versions of MiniZinc.

A solver that can solve under assumptions (see [Section 3.7](https://docs.minizinc.dev/en/2.10.0/assumptions.html#ch-assumptions)) can report an _unsatisfiable core_: a subset of the assumptions that is by itself sufficient to make the model unsatisfiable. Supporting this requires the solver to override the fzn\_assume predicate in its solver-specific library. The core should be printed to the standard output stream as a FlatZinc comment of the following form:

%%%mzn-core: [<entry>, <entry>, ...]

The MiniZinc driver translates each `<entry>` back into the original MiniZinc expression before presenting the core to the user. For this translation to succeed, each `<entry>` must take one of the following two forms:

* An _identifier_ that was passed as an element of the array argument of an fzn\_assume call (i.e. one of the assumption variables).
* An expression of the form `<objective> <op> <const>`, where `<objective>` is the identifier of the objective variable, `<op>` is a comparison operator and `<const>` is a constant. This is used when optimising, to justify that the reported solution is optimal (the objective is bounded by `<const>`).

An entry of any other form (for example an arbitrary auxiliary variable, or a comparison over a non-objective variable) cannot be mapped back to a MiniZinc expression and is reported verbatim.

### 4.3.3.4\. Error and warning output[](#error-and-warning-output "Link to this heading")

Errors and warnings must be output to the standard error stream. When an error occurs, the implementation should exit with a non-zero exit code, signaling failure.

## 4.3.4\. Solver-specific Libraries[](#solver-specific-libraries "Link to this heading")

Constraints in FlatZinc can call standard predicates as well as solver-specific predicates. Standard predicates are the ones that the MiniZinc compiler assumes to be present in all solvers. Without further customisation, the compiler will try to compile the entire model into a set of these standard predicates.

Solvers can use custom predicates and _redefine_ standard predicates by supplying a _solver specific library_ of predicate declarations. Examples of such libraries can be found in the binary distribution of MiniZinc, inside the share/minizinc/gecode and share/minizinc/chuffed directories.

The solver-specific library needs to be made available to the MiniZinc compiler by specifying its location in the solver’s configuration file, see [Section 4.3.6](#sec-cmdline-conffiles).

### 4.3.4.1\. Standard predicates[](#standard-predicates "Link to this heading")

FlatZinc solvers need to support the predicates listed as FlatZinc builtins in the library reference documentation, see [Section 4.2.3](https://docs.minizinc.dev/en/2.10.0/lib-flatzinc.html#ch-lib-flatzinc).

Any standard predicate that is not supported by a solver needs to be _redefined_. This can be achieved by placing a file called redefinitions.mzn in the solver’s MiniZinc library, which can contain alternative definitions of predicates, or define them as unsupported using the abort predicate.

Example for a redefinitions.mzn:

% Redefine float_sinh function in terms of exp
predicate float_sinh(var float: a, var float: b) =
    b == (exp(a)-exp(-a))/2.0;

% Mark float_tanh as unsupported
predicate float_tanh(var float: a, var float: b) =
    abort("The builtin float_tanh is not supported by this solver.");

The redefinition can use the full MiniZinc language. Note, however, that redefining builtin predicates in terms of MiniZinc expressions can lead to problems if the MiniZinc compiler translates the high-level expression back to the redefined builtin.

The reference documentation ([Section 4.2.3](https://docs.minizinc.dev/en/2.10.0/lib-flatzinc.html#ch-lib-flatzinc)) also contains sections on builtins that were added in later versions of MiniZinc. In order to maintain backwards compatibility with solvers that don’t support these, they are organised in redefinition files with a version number attached, such as redefinitions-2.0.mzn. In order to declare support for these builtins, the solver-specific library must contain the corresponding redefinitions file, with the predicates either redefined in terms of other predicates, or declared as supported natively by the solver by providing a predicate declaration without a body.

Example for a redefinitions-2.0.mzn that declares native support for the predicates added in MiniZinc 2.0:

predicate bool_clause_reif(array[int] of var bool: as,
                           array[int] of var bool: bs,
                           var bool: b);
predicate array_int_maximum(var int: m, array[int] of var int: x);
predicate array_float_maximum(var float: m, array[int] of var float: x);
predicate array_int_minimum(var int: m, array[int] of var int: x);
predicate array_float_minimum(var float: m, array[int] of var float: x);

### 4.3.4.2\. Solver-specific predicates[](#solver-specific-predicates "Link to this heading")

Many solvers have built-in support for some of the constraints in the MiniZinc standard library. But without declaring which constraints they support, MiniZinc will assume that they don’t support any except for the standard FlatZinc builtins mentioned in the section above.

A solver can declare that it supports a non-standard constraint by overriding one of the files of the standard library in its own solver-specific library. For example, assume that a solver supports the all\_different constraint on integer variables. In the standard library, this constraint is defined in the file fzn\_all\_different\_int.mzn, with the following implementation:

predicate fzn_all_different_int(array[int] of var int: xs) =
  forall(i,j in index_set(xs) where i < j) ( xs[i] != xs[j] );

A solver, let’s call it _OptiSolve_, that supports this constraint natively can place a file with the same name, fzn\_all\_different\_int.mzn, in its library, and redefine it as follows:

predicate optisolve_alldifferent(array[int] of var int: xs);

predicate fzn_all_different_int(array[int] of var int: xs) =
  optisolve_alldifferent(xs);

When a MiniZinc model that contains the all\_different constraint is now compiled with the _OptiSolve_ library, the generated FlatZinc will contain calls to the newly defined predicate optisolve\_alldifferent.

**Note:** The solver-specific library has been reorganised for MiniZinc version 2.3.0\. Previously, a solver library would contain e.g. the file bin\_packing.mzn in order to override the `bin_packing` constraint. With version 2.3.0, this is still possible (in order to maintain backwards compatibility). However, the predicate `bin_packing` from file bin\_packing.mzn now delegates to the predicate `fzn_bin_packing` in fzn\_bin\_packing.mzn. This enables the `bin_packing` predicate to check that the arguments are correct using assertions, before delegating to the solver-specific predicate. If your solver still uses the old library layout (i.e., overriding bin\_packing.mzn instead of fzn\_bin\_packing.mzn), you should consider updating it to the new standard.

### 4.3.4.3\. Parameter names in solver-specific libraries[](#parameter-names-in-solver-specific-libraries "Link to this heading")

The parameter names in the standard library’s predicate declarations are part of the interface: they are the names by which a constraint’s arguments may be given as named arguments (see [Call Expressions](https://docs.minizinc.dev/en/2.10.0/spec.html#spec-call-expressions)). When a solver redefines a standard predicate, its declaration should use the _same_parameter names as the standard-library declaration. The standard fzn\_all\_different\_int, for instance, names its parameter xs, so a redefinition should too:

predicate fzn_all_different_int(array[int] of var int: xs);   % names match the standard library

Using different names (for example x instead of xs) does not change how the predicate resolves — the compiler matches these low-level predicates by argument type, not by name, so a renamed library behaves exactly as before. It does, however, mean the constraint cannot be reached by those names once named arguments are enabled for native predicates.

To audit a library against the canonical names, compile any model with the \--warn-non-authoritative-names option ([Section 3.1](https://docs.minizinc.dev/en/2.10.0/command%5Fline.html#ch-cmdline)). It reports every predicate declaration whose parameter names differ from the standard library’s body-less declaration for the same signature.

Named arguments are being extended to native predicates in stages, so that existing solver libraries keep working while the ecosystem converges on a common set of names:

1. In the current release, native (body-less) predicates are positional-only. They resolve by argument type, named calls to them are rejected, and \--warn-non-authoritative-names is off by default — so a library with divergent names still works unchanged.
2. In a later release, the warning will be on by default, prompting solver authors to align their libraries.
3. In a release after that, the divergence will become an error and named arguments will be enabled for native predicates.

Solver implementers are encouraged to adopt the standard-library parameter names now, so their libraries are ready when named arguments reach the native layer.

### 4.3.4.4\. Reified and half-reified predicates[](#reified-and-half-reified-predicates "Link to this heading")

A reified constraint is a constraint that is not simply enforced, but whose truth value is bound to a Boolean variable. For example, a MiniZinc expression `var bool: b = all_different(x);` would constrain `b` to be true if and only if the variables `x` take pairwise different values.

If a predicate is called in such a reified context, the MiniZinc compiler will try to find a version of the predicate with `_reif` added to its identifier and an additional `var bool` argument. For the above example, the compiler will try to generate the following FlatZinc code:

var bool: b;
constraint all_different_reif(x, b);

If the `_reif` predicate does not exist, the compiler will try to use the definition of the original predicate. However, this may not be ideal: the original definition may make use of free variables in a `let` expression (which is not allowed in reified contexts), or it may lead to inefficient solving.

Solver libraries should therefore provide reified versions of constraints whenever possible. The library contains files fzn\_\_reif.mzn for this purpose. 

When a reified constraint is used in a _positive context_ (see [Section 2.3.6](https://docs.minizinc.dev/en/2.10.0/predicates.html#pred-context)), the MiniZinc compiler can use a special version, called a half-reified predicate and identified by an `_imp` suffix, instead of the `_reif` predicate. Half-reified predicates essentially represent constraints that are _implied_ by a Boolean variable rather than being equivalent to one. This typically leads to simpler translations or more efficient propagation (e.g., a half-reified `all_different` only needs to _check_ whether it is false, but it never has to implement the negation of the actual constraint).

For example, `constraint y=0 \/ all_different(x)` might be translated as follows:

var bool: X_INTRODUCED_1;
var bool: X_INTRODUCED_2;
constraint int_eq_imp(y,0,X_INTRODUCED_1);
constraint all_different_imp(x, X_INTRODUCED_2);
constraint bool_clause([X_INTRODUCED_1,X_INTRODUCED_2]);

MiniZinc will decide whether to use half-reification case by case based on the availability of the `_imp` predicate. As for reified constraints, it may be benefitial to provide specialised half-reified versions if the solver supports them.

## 4.3.5\. Command-Line Interface and Standard Options[](#command-line-interface-and-standard-options "Link to this heading")

In order to work with the minizinc command line driver, a FlatZinc solver must be an executable (which can include e.g. shell scripts) that can be invoked as follows:

$ <executable-name> [options] model.fzn

where  is the name of the executable. Solvers may support the following standard options: 

\-a[](#cmdoption-a "Link to this definition")

Instructs the solver to report _all_ solutions in the case of satisfaction problems, or print _intermediate_ solutions of increasing quality in the case of optimisation problems.

\-n <i>[](#cmdoption-n "Link to this definition")

Instructs the solver to stop after reporting i solutions (only used with satisfaction problems).

\-i[](#cmdoption-i "Link to this definition")

Instructs the solver to print _intermediate_ solutions of increasing quality (only used with optimisation problems). This option should be supported rather than \-a for solvers which only support printing of intermediate solutions for optimisation problems but no reporting of all solutions for satisfaction problems.

\-f[](#cmdoption-f "Link to this definition")

Instructs the solver to conduct a “free search”, i.e., ignore any search annotations. The solver is not _required_ to ignore the annotations, but it is _allowed_ to do so.

\-s[](#cmdoption-s "Link to this definition")

Print statistics during and/or after the search for solutions. Statistics should be printed as FlatZinc comments to the standard output stream. See [Section 4.3.3.2](#ch-fzn-statistics) for the standard format for statistics.

\-v[](#cmdoption-v "Link to this definition")

Print log messages (verbose solving) to the standard error stream. If solvers choose to print to standard output instead, all messages must be valid comments (i.e., start with a % character).

\-p <i>[](#cmdoption-p "Link to this definition")

Run with i parallel threads (for multi-threaded solvers).

\-r <i>[](#cmdoption-r "Link to this definition")

Use i as the random seed (for any random number generators the solver may be using).

\-t <ms>[](#cmdoption-t "Link to this definition")

Wall time limit ms milliseconds.

## 4.3.6\. Solver Configuration Files[](#solver-configuration-files "Link to this heading")

In order for a solver to be available to MiniZinc, it has to be described in a _solver configuration file_. This is a simple file, in JSON or .dzn format, that contains some basic information such as the solver’s name, version, where its library of global constraints can be found, and a path to its executable. Examples are given in [Section 3.5](https://docs.minizinc.dev/en/2.10.0/solvers.html#ch-solvers).

A solver configuration file must have file extension .msc (for MiniZinc Solver Configuration), and can be placed in any of the following locations:

* In the minizinc/solvers/ directory of the MiniZinc installation. If you install MiniZinc from the binary distribution, this directory can be found at /usr/share/minizinc/solvers on Linux systems, inside the MiniZincIDE application on macOS system, and in the Program Files\\MiniZinc IDE (bundled) folder on Windows.
* In the directory $HOME/.minizinc/solvers on Linux and macOS systems, and the Application Data directory on Windows systems.
* In any directory listed on the MZN\_SOLVER\_PATH environment variable (directories are separated by : on Linux and macOS, and by ; on Windows systems).
* In any directory listed in the mzn\_solver\_path option of the global or user-specific configuration file (see [Section 3.1.4](https://docs.minizinc.dev/en/2.10.0/command%5Fline.html#ch-user-config))
* Alternatively, you can use the MiniZinc IDE to create solver configuration files, see [Section 3.2.5.2](https://docs.minizinc.dev/en/2.10.0/minizinc%5Fide.html#sec-ide-add-solvers) for details.

You can also query the minizinc driver about these directories using the \--config-dirs command line option.

Solver configuration files must be valid JSON or .dzn files. As a JSON file, it must be an object with certain fields. As a .dzn file, it must consist of assignment items.

For example, a simple solver configuration in JSON format could look like this:

{
  "name" : "My Solver",
  "version": "1.0",
  "id": "org.myorg.my_solver",
  "executable": "fzn-mysolver"
}

The same configuration in .dzn format would look like this:

name = "My Solver";
version = "1.0";
id = "org.myorg.my_solver";
executable = "fzn-mysolver";

Here is a list of all configuration options recognised by the configuration file parser. Any valid configuration file must at least contain the fields name, version, id, and executable.

* name (string, required): The name of the solver (displayed, together with the version, when you call minizinc --solvers, and in the MiniZinc IDE).
* version (string, required): The version of the solver.
* id (string, required): A unique identifier for the solver, “reverse domain name” notation.
* executable (string or list of strings, required): The executable for this solver that can run FlatZinc files. This can be just a file name (in which case the solver has to be on the current PATH), an absolute path to the executable, or a relative path (which is interpreted relative to the location of the configuration file). When a list of strings is provided, the first string is treated as the executable and consecutive strings are treated as arguments or flags that are always passed to the executable (i.e., arguments and flags that are not configurable by the solver user).
mznlib (string, default ""): The solver-specific library of global constraints and redefinitions. This should be the name of a directory (either an absolute path or a relative path, interpreted relative to the location of the configuration file). For solvers whose libraries are installed in the same location as the MiniZinc standard library, this can also take the form \-G, e.g., \-Ggecode (this is mostly the case for solvers that ship with the MiniZinc binary distribution). 
* tags (list of strings, default empty): Each solver can have one or more tags that describe its features in an abstract way. Tags can be used for selecting a solver using the \--solver option. There is no fixed list of tags, however we recommend using the following tags if they match the solver’s behaviour:

* "cp": for Constraint Programming solvers
* "mip": for Mixed Integer Programming solvers
* "float": for solvers that support float variables
* "api": for solvers that use the internal C++ API
* stdFlags (list of strings, default empty): Which of the standard solver command line flags are supported by this solver. The standard flags are \-a, \-n, \-i, \-s, \-v, \-p, \-r, \-f, \-t.
* extraFlags (list of list of strings, default empty): Extra command line flags supported by the solver. Each entry must be a list of four strings. The first string is the name of the option (e.g. "--special-algorithm"). The second string is a description that can be used to generate help output (e.g. "which special algorithm to use"). The third string specifies the type of the argument ("int", "bool", "float", "string" or "opt"). The fourth string is the default value. The following types have an additional extended syntax:

* "int:n:m" where n and m are integers, gives lower and upper bounds for the supported values
* "float:n:m" where n and m are floating point numbers, gives lower and upper bounds for the supported values
* "bool:onstring:offstring" specifies strings to add to the command line flag to turn it on (onstring) and off (offstring). E.g., \["-interrupt","whether to catch Ctrl-C","bool:yes:no","yes"\] specifies a command line option that can be called as \-interrupt yes or \-interrupt no. The standard behaviour (just "bool") means that the option is either added to the command line or not.
* "opt:first option:second option:...:last option" specifies a list of possible values for the option
* inputType (string, default FZN, options MZN, FZN, NL, JSON): The type of input expected by the solver.
* supportsMzn (bool, default false): Whether the solver can run MiniZinc directly (i.e., it implements its own compilation or interpretation of the model). \[Deprecated, use inputType\]
* supportsFzn (bool, default true): Whether the solver can run FlatZinc. This should be the case for most solvers. \[Deprecated, use inputType\]
* supportsNL (bool, default false): Whether the solver supports NL input. Used for non-linear solvers. \[Deprecated, use inputType\]
* needsSolns2Out (bool, default true): Whether the output of the solver needs to be passed through the MiniZinc output processor.
* needsMznExecutable (bool, default false): Whether the solver needs to know the location of the MiniZinc executable. If true, it will be passed to the solver using the mzn-executable option.
* needsStdlibDir (bool, default false): Whether the solver needs to know the location of the MiniZinc standard library directory. If true, it will be passed to the solver using the stdlib-dir option.
* isGUIApplication (bool, default false): Whether the solver has its own graphical user interface, which means that MiniZinc will detach from the process and not wait for it to finish or to produce any output.
* isInteractive (bool, default false): Whether the solver runs an interactive command-line session. When set, MiniZinc lets the solver read the user’s terminal stdin directly (so the user can type commands to it) and echoes the solver’s stdout back verbatim, _except_ for solution blocks. A solution block is the text bracketed by the marker lines %%%mzn-sol-begin and %%%mzn-sol-end; the lines between those markers must be standard FlatZinc solution output (variable assignments terminated by \----------) and are passed through the normal output processing (so they are mapped through the model’s output item). The marker lines themselves are consumed. This is equivalent to passing \--fzn-interactive to the generic FlatZinc driver. Because the solver’s stdout is a pipe (not a terminal) in this mode, an interactive solver must flush its prompts and replies.

## 4.3.7\. Grammar[](#grammar "Link to this heading")

This is the full grammar for FlatZinc. It is a proper subset of the MiniZinc grammar (see [Section 4.1.14](https://docs.minizinc.dev/en/2.10.0/spec.html#spec-grammar)). However, instead of specifying all the cases in the MiniZinc grammar that do _not_ apply to FlatZinc, the BNF syntax below contains only the relevant syntactic constructs. It uses the same notation as in [Section 4.1.2](https://docs.minizinc.dev/en/2.10.0/spec.html#spec-syntax-notation).

% A FlatZinc model
<model> ::=
  [ <predicate-item> ]*
  [ <par-decl-item> ]*
  [ <var-decl-item> ]*
  [ <constraint-item> ]*
  <solve-item>

% Predicate items
<predicate-item> ::= "predicate" <identifier> "(" [ <pred-param-type> ":" <identifier> "," ... ] ")" ";"

% Identifiers
<identifier> ::= [A-Za-z][A-Za-z0-9_]*

<basic-par-type> ::= "bool"
                   | "int"
                   | "float"
                   | "set of int"

<basic-var-type> ::= "var" <basic-par-type>
                   | "var" <int-literal> ".." <int-literal>
                   | "var" "{" <int-literal> "," ... "}"
                   | "var" <float-literal> ".." <float-literal>
                   | "var" "set" "of" <int-literal> ".." <int-literal>
                   | "var" "set" "of" "{" [ <int-literal> "," ... ] "}"

<array-var-type> ::= "array" "[" <index-set> "]" "of" <basic-var-type>

<index-set> ::= "1" ".." <int-literal>

<basic-pred-param-type> ::= <basic-par-type>
                          | <basic-var-type>
                          | <int-literal> ".." <int-literal>
                          | <float-literal> ".." <float-literal>
                          | "{" <int-literal> "," ... "}"
                          | "set" "of" <int-literal> .. <int-literal>
                          | "set" "of" "{" [  <int-literal> "," ... ] "}"

<pred-param-type> ::= <basic-pred-param-type>
                    | "array" "[" <pred-index-set> "]" "of" <basic-pred-param-type>

<pred-index-set> ::= <index-set>
                   | "int"

<basic-literal-expr> ::= <bool-literal>
                       | <int-literal>
                       | <float-literal>
                       | <set-literal>

<basic-expr> ::= <basic-literal-expr>
              | <var-par-identifier>

<expr>       ::= <basic-expr>
               | <array-literal>

<var-par-identifier> ::= [A-Za-z_][A-Za-z0-9_]*

% Boolean literals
<bool-literal> ::= "false"
                 | "true"

% Integer literals
<int-literal> ::= [-]?[0-9]+
                | [-]?0x[0-9A-Fa-f]+
                | [-]?0o[0-7]+

% Float literals
<float-literal> ::= [-]?[0-9]+.[0-9]+
                  | [-]?[0-9]+.[0-9]+[Ee][-+]?[0-9]+
                  | [-]?[0-9]+[Ee][-+]?[0-9]+

% Set literals
<set-literal> ::= "{" [ <int-literal> "," ... ] "}"
                | <int-literal> ".." <int-literal>
                | "{" [ <float-literal> "," ... ] "}"
                | <float-literal> ".." <float-literal>

<array-literal> ::= "[" [ <basic-expr> "," ... ] "]"

<par-array-literal> ::= "[" [ <basic-literal-expr> "," ... ] "]"

% Parameter declarations

<par-decl-item> ::= "array" "[" <index-set> "]" "of" <basic-par-type> ":" <var-par-identifier> "=" <par-array-literal> ";"

% Variable declarations

<var-decl-item> ::= <basic-var-type> ":" <var-par-identifier> <annotations> [ "=" <basic-expr> ] ";"
                  | <array-var-type> ":" <var-par-identifier> <annotations> "=" <array-literal> ";"

% Constraint items

<constraint-item> ::= "constraint" <identifier> "(" [ <expr> "," ... ] ")" <annotations> ";"

% Solve item

<solve-item> ::= "solve" <annotations> "satisfy" ";"
               | "solve" <annotations> "minimize" <basic-expr> ";"
               | "solve" <annotations> "maximize" <basic-expr> ";"

% Annotations

<annotations> ::= [ "::" <annotation> ]*

<annotation> ::= <identifier>
               | <identifier> "(" <ann-expr> "," ... ")"

<ann-expr>   := <basic-ann-expr>
              | "[" [ <basic-ann-expr> "," ... ] "]"

<basic-ann-expr>   := <basic-literal-expr>
                    | <var-par-identifier>
                    | <string-literal>
                    | <annotation>

<string-contents> ::= ([^"\n\] | \[^\n(])*

<string-literal> ::= """ <string-contents> """

% End of FlatZinc grammar