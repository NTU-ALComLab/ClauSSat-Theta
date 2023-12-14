# ClauSSat
This is a SSAT(Θ) solver extended from the SSAT solver ClauSSat.
To compile, first configure CUDD package
```
$ cd src/cudd/; ./configure --enable-dddmp --enable-obj --enable-static; cd ../../;
```
And then compile by typing
```
$ make
```
To run, use the following command
```
$ ./claussat -s [SSAT(Θ)_file]
```

# SSAT(Θ) Benchmarks
All the instances used in the experiments can be found under the directory "benchmarks/TSSAT/".
The instances in the folder "MAX_PCTL" encoded the parameter synthesis problem while other intances
are generated from SSAT instances.
