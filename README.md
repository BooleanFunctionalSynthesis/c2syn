This is another implementation of the c2syn paper:

Knowledge Compilation for Boolean Functional Synthesis
S. Akshay, Jatin Arora, Supratik Chakraborty, S. Krishna, Divya Raghunathan and Shetal Shah
In Formal Methods in Computer-Aided Design (FMCAD), Oct. 2019 

-----
Download the code using git clone 

To make:

1. First go to dependencies/abc and do a make; make libabc.a
2. Then go to dependencies/dsharp and do a make; make libdsharp.a
3. Then in dependencies/bfss and do make; make libcombfss.a
4. Now run a make in this directory. It will generate a binary c2syn in the bin directory

To run:

To run c2syn use the following command ${PATH-TO-c2syn}/c2syn {benchmark-name}.qdimacs
To verify the {benchmark-name}.syn.blif file use:
    ${PATH-TO-c2syn}/verify {benchmark-name}.qdimacs {benchmark-name}.syn.blif {benchmark-name}_varstoelim.txt

Please see the script test/runc2syn for more details.

Known issues:

1. The generated synNNF file ({benchmark-name}.syn.blif) can be quite large. In this case, we are currently unable to verify these files as they are too big for ABC to read them.
