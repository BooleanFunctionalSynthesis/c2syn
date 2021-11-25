This is an alternate implementation of the c2syn paper:

Knowledge Compilation for Boolean Functional Synthesis
S. Akshay, Jatin Arora, Supratik Chakraborty, S. Krishna, Divya Raghunathan and Shetal Shah
In Formal Methods in Computer-Aided Design (FMCAD), Oct. 2019 

-----
Download the code using git clone 

To make:

To make c2syn, we first need to make the libraries it is dependent on. This can be done by running the install.sh script or
alternatively using the following commands:
1. cd dependencies/abc; make; make libabc.a; cd ../../
2. cd dependencies/dsharp; make; make libdsharp.a; cd ../../
3. cd dependencies/bfss; make; make libcombfss.a; cd ../../
4. Finally do a make in the base directory. This will generate the binary c2syn in the bin directory

To run:

To run c2syn use the following command ${PATH-TO-c2syn}/c2syn {benchmark-name}.qdimacs

If you want the synNNF representation printed to a file please use the option --dumpResult while running the command above.
The synNNF representation is printed in {benchmark-name}.syn.blif file.

To verify the {benchmark-name}.syn.blif file use:
    ${PATH-TO-c2syn}/verify {benchmark-name}.qdimacs {benchmark-name}.syn.blif {benchmark-name}_varstoelim.txt

Please see the script test/runc2syn for more details.

Known issues:

1. The generated synNNF file ({benchmark-name}.syn.blif) can be quite large.  
For large representations,  we are currently unable to verify these files as they are too big for ABC to read them.
