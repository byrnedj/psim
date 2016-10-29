/*BEGIN_LEGAL 
Intel Open Source License 

Copyright (c) 2002-2016 Intel Corporation. All rights reserved.
 
Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

Redistributions of source code must retain the above copyright notice,
this list of conditions and the following disclaimer.  Redistributions
in binary form must reproduce the above copyright notice, this list of
conditions and the following disclaimer in the documentation and/or
other materials provided with the distribution.  Neither the name of
the Intel Corporation nor the names of its contributors may be used to
endorse or promote products derived from this software without
specific prior written permission.
 
THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE INTEL OR
ITS CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
END_LEGAL */
/* ===================================================================== */
/*
  @ORIGINAL_AUTHOR: Daniel Byrne
*/

/* ===================================================================== */
/*! @file
 *  This file contains an ISA-portable PIN tool for counting:
 *  -Dynamic instructions
 *  -Average BB size
 *  -Percent branches
 *      -percent forward
 *  -Percent memory
 *  -Percent taken branches
 *      -percent forward
 *      -percent backward
 *
 *
 */

#include <map>
#include <iostream>
#include <fstream>
#include <iomanip>
#include <fstream>
#include <string>

#include "pin.H"
#include "portability.H"
#include "pin_profile.H"

#include <algorithm> // for sort
#include <vector>
#include <queue> 

/* ===================================================================== */
/* Global Variables */
/* ===================================================================== */


//counts
double ins_count = 0;
double branch_count = 0;
double fwd_branch_count = 0;
double mem_count = 0;
double BB_count = 0;
double taken_branch_count = 0;
double fwd_taken_branch_count = 0;
double bck_taken_branch_count = 0;
double compute_count = 0;
double dep_dist = 0;

double ins_local16 = 0;
double ins_local64 = 0;
double ins_local256 = 0;
double ins_local4096 = 0;

double data_local16 = 0;
double data_local64 = 0;
double data_local256 = 0;
double data_local4096 = 0;

double dep_dist1 = 0;
double dep_dist2 = 0;
double dep_dist4 = 0;
double dep_dist8 = 0;
double dep_dist16 = 0;
double dep_dist32 = 0;
double dep_distgt32 = 0;

double BB_size = 0;


typedef map<ADDRINT,UINT64> ADDR_CNT_MAP;

ADDR_CNT_MAP InsLocality;
ADDR_CNT_MAP DataLocality;
ADDR_CNT_MAP DataDep;


std::ofstream out;

/* ===================================================================== */
/* Commandline Switches */
/* ===================================================================== */

KNOB<string> KnobOutputFile(KNOB_MODE_WRITEONCE,         "pintool",
                            "o", "program_analysis.out", "specify profile file name");

/* ===================================================================== */
/* Print Help Message                                                    */
/* ===================================================================== */

INT32 Usage()
{
    cerr <<
        "This tool prints out the number of dynamic instructions executed to stderr.\n"
        "\n";

    cerr << KNOB_BASE::StringKnobSummary();
    cerr << endl;

    return -1;
}

VOID do_ins_locality(ADDRINT iaddr)
{
    //ins temporal locality
    //look for 2 consecutive accesses to the
    //same memory address -> reuse distance
    UINT64 pcount = InsLocality[iaddr];
    UINT64 reuse_dist = ins_count - pcount;

    //update the locality
    InsLocality[iaddr] = ins_count;

    if (reuse_dist < 16)
        ins_local16++;
    else if (reuse_dist < 64)
        ins_local64++;
    else if (reuse_dist < 256)
        ins_local256++;
    else if (reuse_dist < 4096)
        ins_local4096++;
    
    ins_count++;

}

/* ===================================================================== */

VOID  do_call_indirect(ADDRINT target, ADDRINT curr, BOOL taken)
{
    if( !taken )
    {
        //is forward?
        if (target > curr)
            fwd_branch_count++;
        branch_count++;
    }
    else
    {
        //is forward?
        if (target > curr)
        {    
            fwd_taken_branch_count++;
            fwd_branch_count++;
        }
        else
            bck_taken_branch_count++;
        branch_count++;
        taken_branch_count++;
    }

    do_ins_locality(curr);

}

/* ===================================================================== */

VOID Trace(TRACE trace, VOID *v)
{
    for (BBL bbl = TRACE_BblHead(trace); BBL_Valid(bbl); bbl = BBL_Next(bbl))
    {
        INS tail = BBL_InsTail(bbl);

        if( INS_IsCall(tail) )
        {
            INS_InsertCall(tail, IPOINT_BEFORE, AFUNPTR(do_call_indirect),
                               IARG_BRANCH_TARGET_ADDR, IARG_INST_PTR, IARG_BRANCH_TAKEN, IARG_END);
        }
        else
        {
            // sometimes code is not in an image
            RTN rtn = TRACE_Rtn(trace);
            
            // also track stup jumps into share libraries
            if( RTN_Valid(rtn) && !INS_IsDirectBranchOrCall(tail) && 
                    ".plt" == SEC_Name( RTN_Sec( rtn ) ))
            {
                INS_InsertCall(tail, IPOINT_BEFORE, AFUNPTR(do_call_indirect),
                               IARG_BRANCH_TARGET_ADDR, IARG_INST_PTR, IARG_BRANCH_TAKEN, IARG_END);
            }
        }

        //BB stats
        BB_count++;
        BB_size += BBL_NumIns(bbl);
    }
}

/* ===================================================================== */

VOID MemRead(ADDRINT ea, ADDRINT iaddr)
{

    //look for true deps
    //waddr is the last address written to
    UINT64 wcount = DataDep[ea];

    //figure out how many instructions were between them
    UINT64 dep_dist = ins_count - wcount;
    
    if (dep_dist ==  1)
        dep_dist1++;
    else if (dep_dist <= 2)
        dep_dist2++;
    else if (dep_dist <= 4)
        dep_dist4++;
    else if (dep_dist <= 8)
        dep_dist8++;
    else if (dep_dist <= 16)
        dep_dist16++;
    else if (dep_dist <= 32)
        dep_dist32++;
    else 
        dep_distgt32++;
    
    //data temporal locality
    //look for 2 consecutive accesses to the
    //same memory address -> reuse distance
    UINT64 pcount = DataLocality[ea];
    UINT64 reuse_dist = mem_count - pcount;

    if (reuse_dist < 16)
        data_local16++;
    else if (reuse_dist < 64)
        data_local64++;
    else if (reuse_dist < 256)
        data_local256++;
    else if (reuse_dist < 4096)
        data_local4096++;
    
    //update the locality
    DataLocality[ea] = mem_count;

    do_ins_locality(iaddr);

    mem_count++;
}

/* ===================================================================== */

VOID MemWrite(ADDRINT ea, ADDRINT iaddr)
{

    //record write at this inst
    DataDep[ea] = ins_count;

    //data temporal locality
    //look for 2 consecutive accesses to the
    //same memory address -> reuse distance
    //cold, reuse dist = 0
    //just use mem count
    UINT64 pcount = DataLocality[ea];
    UINT64 reuse_dist = mem_count - pcount;

    if (reuse_dist < 16)
        data_local16++;
    else if (reuse_dist < 64)
        data_local64++;
    else if (reuse_dist < 256)
        data_local256++;
    else if (reuse_dist < 4096)
        data_local4096++;
    
    //update the locality
    DataLocality[ea] = mem_count;

    do_ins_locality(iaddr);

    mem_count++;
}

/* ===================================================================== */

VOID ComputeIns(ADDRINT iaddr)
{
    compute_count++;
    do_ins_locality(iaddr);
}




/* ===================================================================== */

VOID Instruction(INS ins, VOID *v)
{
    int opcodes[20] = {8,145,148,149,160,181,182,184,212,213,236,237,
                     261,262,440,443,444,761,764,765}; 

    OPCODE op = INS_Opcode(ins);
    int i;
    bool compute = false;
    for (i = 0; i < 20; i++)
    {
        if (opcodes[i] == op)
            compute = true;
    }

    if ( INS_IsMemoryWrite(ins) && INS_IsStandardMemop(ins))
    {
        INS_InsertPredicatedCall(
                ins, IPOINT_BEFORE, (AFUNPTR) MemWrite,
                IARG_MEMORYWRITE_EA,
                IARG_INST_PTR,
                IARG_END);
    }
    else if (INS_IsMemoryRead(ins) && INS_IsStandardMemop(ins))
    {    
        INS_InsertPredicatedCall(
                ins, IPOINT_BEFORE, (AFUNPTR) MemRead,
                IARG_MEMORYREAD_EA,
                IARG_INST_PTR,
                IARG_END);
    } 
    else if (compute)
    {
        INS_InsertCall(ins,IPOINT_BEFORE, (AFUNPTR)ComputeIns, IARG_INST_PTR, IARG_END);
    }
    else
    {
        INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)do_ins_locality, IARG_INST_PTR, IARG_END);
    }
    
}

/* ===================================================================== */

VOID Fini(INT32 code, VOID *v)
{

    
    

    double per_mem = (mem_count/ins_count);
    double per_branch = (branch_count/ins_count);
    double comp_ratio = (compute_count/mem_count);
    double bbsize = (BB_size/BB_count);
    double per_fwd = (fwd_branch_count/branch_count);
    double per_taken = (taken_branch_count/branch_count);
    double per_fwd_taken = (fwd_taken_branch_count/taken_branch_count);
    double per_back_taken = (bck_taken_branch_count/taken_branch_count);

    double d64_ratio  = (data_local64/data_local16);
    double d256_ratio  = (data_local256/data_local16);
    double d4096_ratio  = (data_local4096/data_local16);
    
    double i64_ratio  = (ins_local64/ins_local16);
    double i256_ratio  = (ins_local256/ins_local16);
    double i4096_ratio  = (ins_local4096/ins_local16);

    out << "mem,branch,comp_mem,bbsize,fwd,taken,fwd_taken,back_taken,"
           "d-tlocality16,d-tlocality64,d-tlocality256,d-tlocality4096," <<
           "d-tloc64/d-tloc16,d-tloc256/d-tloc16,d-tloc4096/d-tloc16," <<
           "dep_dist1,dep_dist2,dep_dist4,dep_dist8,dep_dist16,dep_dist32,dep_distgt32," <<
           "i-tlocality16,i-tlocality64,i-tlocality256,i-tlocality4096," <<
           "i-tloc64/i-tloc16,i-tloc256/i-tloc16,i-tloc4096/i-tloc16," << endl;

    out << per_mem << "," << per_branch << "," << comp_ratio << "," << bbsize << "," << per_fwd
        << "," << per_taken << "," << per_fwd_taken << "," << per_back_taken << ","
        << data_local16 << "," << data_local64 << "," << data_local256 << "," << data_local4096
        << "," << d64_ratio << "," << d256_ratio << "," << d4096_ratio 
        << "," << dep_dist1
        << "," << dep_dist2
        << "," << dep_dist4
        << "," << dep_dist8
        << "," << dep_dist16
        << "," << dep_dist32
        << "," << dep_distgt32 << ","
        << ins_local16 << "," << ins_local64 << "," << ins_local256 << "," << ins_local4096
        << "," << i64_ratio << "," << i256_ratio << "," << i4096_ratio << endl; 

    out.close();
    
}

/* ===================================================================== */
/* Main                                                                  */
/* ===================================================================== */

int main(int argc, char *argv[])
{
    if( PIN_Init(argc,argv) )
    {
        return Usage();
    }
    
    out.open(KnobOutputFile.Value().c_str());
    
    //resuse distance, memory ops etc total count...
    INS_AddInstrumentFunction(Instruction, 0);
    //basic blocks and jumps
    TRACE_AddInstrumentFunction(Trace, 0);
    PIN_AddFiniFunction(Fini, 0);

    // Never returns
    PIN_StartProgram();
    
    return 0;
}

/* ===================================================================== */
/* eof */
/* ===================================================================== */
