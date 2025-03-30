To test electrod backtrace functionality, run an example with no_analysis:

```
./electrod.exe test/micro.elo --kg --na  
```

It will generate a file `test/micro.info` with electrod's state and an SMV file with the model.

Run your tool to produce an example, e.g., as shown in `test/micro.out`.

```
./electrod.exe test/micro.out --bt test/micro.info
```

It will generate a `test/micro.xml` file.