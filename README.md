# README
## What is this repository for?

* *lightblue* is a multi-lingual CCG parser with DTS representations
* Copyright owner: Daisuke Bekki and Bekki Laboratory

## Installing lightblue
### Prerequisite 1: Haskell Stack
In Linux:
```
$ wget -qO- https://get.haskellstack.org/ | sh
```
In Mac:
```
$ brew install haskell-stack
```
See https://docs/haskellstack.org/en/stable/README/#how-to-install for details.

### Prerequisite 2: Installation of Japanese morphological analyzer
One of the following Japanese morphological analyzers must be installed before executing *lightblue*.

- [KWJA](https://github.com/ku-nlp/kwja)

- [JUMAN](http://nlp.ist.i.kyoto-u.ac.jp/EN/index.php?JUMAN) (>= version 7.0) 

- [JUMAN++](https://nlp.ist.i.kyoto-u.ac.jp/?JUMAN%2B%2B) 

### Prerequisite 3: Installation of English morphological analyzer
The following English morphological analyzers must be installed before executing *lightblue*.

- [NLTK](https://www.nltk.org/install.html) & [NLTK data](https://www.nltk.org/data.html)

### Download lightblue
Do the following in the directory under which you'd like to install *lightblue*.
```
$ git clone --depth=1 https://github.com/DaisukeBekki/lightblue.git
```
This operation will create, under the current directory, a new directory *lightblue*.  Henceforth we will refer to the full path to this directory as &lt;lightblue&gt;.

### Configuration and Installation
You need to add the environment variable LIGHTBLUE and set its value as &lt;lightblue&gt;.  You may add the line `export LIGHTBLUE=<lightblue>` to .bashrc, .bash.profile, .bash_profile, or whatever configuration file for your shell.  Then move to &lt;lightblue&gt; and do the following:
```
$ cd <lightblue>
$ stack build
```

Set the permission of the shell scripts `lightblue` to executable.
```
$ chmod 755 lightblue
```

## Running lightblue
### Quick Start

To parse a Japanese sentence and get a parsing result in a text format, execute:
```
$ echo 太郎がパンを食べた。 | ./lightblue jp parse -s text
```

To parse an English sentence and get a parsing result, execute:
```
$ echo John loves Mary. | ./lightblue en parse -s text
```

To see a parsing result in HTML formal, execute (choose your browser):
```
$ echo 太郎がパンを食べた。 | ./lightblue jp parse -s html > result.html; firefox result.html
```

If you have a text file (one sentence per line) &lt;corpusfile&gt;, then you can feed its path to *lightblue* by:
```
$ ./lightblue jp parse -s html -f <corpusfile>
```

To parse a JSeM file and execute inferences therein, then you can feed it to *lightblue* by:
```
$ ./lightblue jp jsem -f <jsemfile>
```

To execute an inference of the FraCaS GF treebank, give the number of the problem:
```
$ export FRACAS_TREEBANK=<path>/FraCaSBankI.gf
$ export FRACAS_XML=<path>/fracas.xml
$ ./lightblue gf --problem 49
```
This translates the abstract syntax trees of problem 49 into UDTT pretermes and
prints, in this order, the sentences of the test suite, the settings of the run,
their trees, the signature, their semantic representations, the type check query
and diagram of each sentence, the two proof search queries with their diagrams,
and finally the predicted and the gold label.  To read the proof diagrams in a
browser, ```--open``` writes an html file and opens it:
```
$ ./lightblue gf --problem 49 --open
```
The two files are distributed separately from lightblue:
[FraCaSBankI.gf](https://github.com/heatherleaf/FraCaS-treebank) holds the trees,
and `fracas.xml` (Bill MacCartney) holds the sentences and the gold answers.
Their paths may also be given with ```--treebank``` and ```--answers```.

### Usage
The syntax of the lightblue command is as follows:
```
./lightblue <lang> <lang's local options> <command> <command's local options> <global options>
```
The ```gf``` command is the exception: it needs no morphological analyzer and no
input text, so it takes neither a language nor the global options.
```
./lightblue gf <gf's local options>
```

|Lang    |                           |
|:-------|:--------------------------|
|```jp```|Japanese                   |
|```en```|English (no local options) |

|Local Options for ```jp```                   |Default   | Description                   |
|:--------------------------------------------|:---------|:------------------------------|
|```-m``` or ```--ma {juman\|jumanpp\|kwja}```|```kwja```|Specify morphological analyzer |
|```--filter {knp\|kwja\|none}```             |```none```|Specify node filter            |

|Command         |                                                                       |
|:---------------|:----------------------------------------------------------------------|
|```parse```     |Parse Sentences and returns parsing results.                           |
|```jsem```      |Parse a JSeM file and execute inferences.                              |
|```numeration```|Shows the list of lexical items prepared for parsing the given sentence|
|```gf```        |Execute an inference of the FraCaS GF treebank (takes no ```<lang>```).|
|```version```   |Print the lightblue version.                                           |
|```stat```      |Print the lightblue statistics.                                        |

Each of ```parse ```, ```jsem``` and ```gf``` commands has a set of local options.

|Local Options for ```parse```                     |Default   |Description                                                    |  
|:-------------------------------------------------|:---------|:--------------------------------------------------------------|
|```-o``` or ```--output {tree\|postag}```         |```tree```|Specify the output content.<br>```tree```: Outputs parse trees and their type check results.<br> ```postag```: Outputs only lexical items (Use lightblue a part-of-speech tagger) |

|Local Options for ```jsem```                      |Default   |Description                           |  
|:-------------------------------------------------|:---------|:-------------------------------------|
|```--jsemid <text>```                             |```all``` |Skip JSeM data the JSeM ID of which is not equial to this value.           |
|```--nsample <int>```                             |```-1```  |Specify a number of JSeM data to process (A negative value means all data) |

|Local Options for ```gf```                        |Default   |Description                           |
|:-------------------------------------------------|:---------|:-------------------------------------|
|```--problem <int>```                             |          |The number (1 to 346) of the FraCaS problem to run. Required. |
|```--treebank <filepath>```                       |```$FRACAS_TREEBANK```|Path of ```FraCaSBankI.gf```, which holds the abstract syntax trees. |
|```--answers <filepath>```                        |```$FRACAS_XML```|Path of ```fracas.xml```, which holds the sentences and the gold answers. |
|```-s``` or ```--style {text\|html}```            |```text```|Show results in the specified format. ```html``` renders the pretermes and the diagrams in MathML. |
|```-o``` or ```--output <filepath>```             |          |Write results to &lt;filepath&gt; instead of stdout. |
|```--open```                                      |          |Write an html file and open it in a browser. Implies ```-s html```, and writes to ```fracas<int>.html``` unless ```-o``` says otherwise. |
|```-p``` or ```--prover {Wani\|Null}```           |```Wani```|Choose a prover. |
|```--nproof <int>```                              |```1```   |Show N-best proof diagram for each proof search (A negative value means all diagrams) |
|```--maxdepth <int>```                            |```5```   |Set the maximum search depth in proof search |
|```--maxtime <int>```                             |```100000```|Set the maximum search time in proof search |
|```--noDiagram```                                 |          |If specified, show no type check and proof diagram. |
|```--verbose```                                   |          |Show type infer/check logs in stderr. |

The global options are common to all commands.

|Global Options                                    |Default   |Description                                                     |
|:------------------------------------------------|:---------|:---------------------------------------------------------------|
|```-s``` or ```--style {text\|tex\|xml\|html\|express}``` |```text```|Show results in the specified format. ```express``` launches an interactive UI.                     |
|```-p``` or ```--prover {Wani\|Null}```          |```Wani```|Choose a prover.<br>```Wani```: Use Wani prover (Daido and Bekki 2020)<br>```None```: Use the null prover (that always returns no diagrams).|
|```-f``` or ```--file <filepath>```              |          |Read input texts from <filepath><br>(Specify '-' to use stdin) |
|```-b``` or ```--beam <int>```                   |```32```  |Set the beam width to <int>                                     |
|```--nparse <int>```                             |```1```  |Search only N-best parse trees for each sentence (A negative value means all trees) |                      |
|```--ntypecheck <int>```                         |```1```  |Search only N-best diagrams for each type checking of a logical form (A negative value means all diagrams) |
|```--nproof <int>```                             |```-1```  |Search only N-best diagrams for each proof search (A negative value means all diagrams) |
|```--maxdepth <int>```                           |```5```   |Set the maximum search depth in proof search (default: 9) |
|```--maxtime <int>```                            |```10000``` |Set the maximum search time in proof search (default: 10000) |
|```--noTypeCheck```                              |          |If specified, show no type checking diagram for each sentence.|
|```--noInference```                              |          |If specified, execute no inference for each discourse.|
|```--time```                                     |          |Show the execution time in stderr.|
|```--verbose```                                  |          |Show type infer/check logs in stderr.|

|Specific Options for ```express```                      |Default   |Description                           |
|:-------------------------------------------------|:---------|:-------------------------------------|
|```--depth <int>```                      | ```2``` |Set expansion depth of syntactic structures|
|```--noShowCat```                        |     |If specified, hide syntactic categories|
|```--noShowSem```                        |     |If specified, hide semantics|
|```--leafVertical```                     |     |If specified, list lexical items vertically|
|```--lexicalPos {top\|bottom\|none}```  | ```top``` |Position of Lexical Items section. `top`: at the very top, `bottom`: at the very bottom, `none`: hide.|
|```--browser {chrome\|firefox\|default}``` | ```default``` |Choose the browser to launch the Express UI. If omitted, the system default browser is used.|

### For developpers ###
Installing Haskell-mode for Emacs will help.
```
$ sudo apt install haskell-mode
```

The following command creates an HTML document at: `<lightblue>/haddock/doc/html/lightblue/index.html`

```
$ stack build --haddock
```

## Contact ##

* Repo owner: [Daisuke Bekki](https://daisukebekki.github.io/)
