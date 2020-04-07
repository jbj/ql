import semmle.code.cpp.File

select sum(File f | any() | f.getMetrics().getNumberOfLinesOfCode())
