# ClauSSat(Θ)
This is an SSAT(Θ) solver extended from the SSAT solver ClauSSat.
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
The instances in the folder "MAX_PCTL" encoded the parameter synthesis problem while other instances
are generated from SSAT instances.


## Reference
* [AAAI'24 paper](https://ojs.aaai.org/index.php/AAAI/article/view/28637):
  ```
  @inproceedings{Fan_Jiang_2024,
      author     = {Fan, Yu-Wei and Jiang, Jie-Hong R.},
      title      = {Unifying Decision and Function Queries in Stochastic Boolean Satisfiability},
      booktitle  = {Proceedings of the AAAI Conference on Artificial Intelligence},
      DOI        = {10.1609/aaai.v38i8.28637},
      year       = {2024}
   }
  ```

## Contact
If you have any problems or suggestions, please create an issue or contact us at r11943096@ntu.edu.tw
