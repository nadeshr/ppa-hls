open_project proj_test

# Add design files
add_files test.c
# Add test bench & files
add_files -tb tb.c

# Set the top-level function
set_top test

# Create a solution
open_solution solution1
# Define technology and clock rate
set_part  {xc7k160tfbg484-1}
create_clock -period 4

set ::LLVM_CUSTOM_CMD {$LLVM_CUSTOM_OPT -load ../pointer-aliasing2/LLVMPtsTo.so -mem2reg -ptsTo $LLVM_CUSTOM_INPUT -o $LLVM_CUSTOM_OUPUT}

#set ::LLVM_CUSTOM_CMD {cp $LLVM_CUSTOM_OUTPUT output.bc}

#llvm-dis output.bc 

csim_design
csynth_design
cosim_design

exit
