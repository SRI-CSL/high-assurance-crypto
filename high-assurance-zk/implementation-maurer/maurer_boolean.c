#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
#include <inttypes.h>
#include <limits.h>
#include <string.h>

#define CAML_NAME_SPACE
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/fail.h>
#include <caml/callback.h>
#include <caml/custom.h>
#include <caml/intext.h>
#include <caml/threads.h>

/* THESE ARE THE JASMIN GENERATED ROUTINES */
extern void input_start5(uint64_t*,uint64_t*,uint64_t*);
extern uint64_t  input_end5(uint64_t*,uint64_t*,uint64_t);

extern void const_start5(uint64_t*,uint64_t*);
extern uint64_t const_end5(uint64_t*,uint64_t*,uint64_t);
extern uint64_t Smult5(uint64_t*,uint64_t,uint64_t,uint64_t);

extern uint64_t add5(uint64_t*,uint64_t,uint64_t,uint64_t);

extern void mult_start5(uint64_t*,uint64_t,uint64_t,uint64_t*,uint64_t*);
extern uint64_t mult_end5(uint64_t*,uint64_t*,uint64_t);

extern void out_start5(uint64_t*,uint64_t,uint64_t*);
extern void out_end5(uint64_t*,uint64_t*,uint64_t);

extern void dispatch(uint64_t*,uint64_t*,uint64_t*,uint64_t*,uint64_t*);
/* THESE ARE THE JASMIN GENERATED ROUTINES */

const int rawShareSize = 1; /* Each Zp is 1 x 64 bit words */
const int nRawShares = 10;  /* Each Maurer share uses 6 out of 10 shares */
const int nRawSharesPP = 6; /* Each Maurer share uses 6 out of 10 shares */
const int nParties = 5;     /* There are 5 parties */

// ** Auxiliary Macros: all sizes in 64-bit words
// *******************************************************************************************************************************

const int randSharingSize = (nRawShares-1)*rawShareSize;
const int shareSize = nRawSharesPP*rawShareSize;
const int sharingSize = shareSize*nParties;
const int viewRowSize = randSharingSize+sharingSize;
const int stateRowSize = shareSize;

const int commitKeySize = 16; /* bytes */

int viewSize(int n_total_wires) { return (n_total_wires+1) * viewRowSize + 1; }
int stateSize(int n_total_wires) { return (n_total_wires) * stateRowSize; }

void print_raw_share(uint64_t* share) {
      printf("(");
      for(int sp=0;sp<rawShareSize;sp++) printf("%lld,",share[sp]);
      printf(") ");
}

void print_status(uint64_t* state, int n_total_wires){
  
  printf("\nState:\n");
  
  for(int w = 0;w<n_total_wires;w++){
    uint64_t* wire = state + w * stateRowSize;
    for(int s = 0;s<nRawSharesPP;s++){
      uint64_t* share = wire + s * rawShareSize;
      print_raw_share(share);
    }
    printf("\n");
  }
}

void print_msg(uint64_t* messages){
  printf("\nJasmin msg:\n");
    for(int s=0;s<nRawSharesPP;s++){
      uint64_t* messageShare = messages + s*rawShareSize;
      print_raw_share(messageShare);
    }
    printf("\n");
}

void print_messages(uint64_t* messages){
  printf("\nJasmin Messages:\n");
  for(int mp=0;mp<nParties;mp++){
    uint64_t* messageParty = messages + mp*shareSize;
    for(int s=0;s<nRawSharesPP;s++){
      uint64_t* messageShare = messageParty + s*rawShareSize;
      print_raw_share(messageShare);
    }
    printf("\n");
  }
}

void print_rand(uint64_t* rand){
  printf("\nRandoms: \n");
  for(int s = 0;s<nRawShares-1;s++){
    uint64_t* share = rand + s*rawShareSize;
    print_raw_share(share);
  }
  printf("\n");
}

void print_View(uint64_t* viewParty, int n_total_wires){
    printf("\n\nView PARTY:\n");
  
    for(int w = 0;w<(n_total_wires+1);w++){
    printf("\n\nWire %d:\n",w);
      uint64_t* row = viewParty + w*viewRowSize;
    print_rand(row);
    uint64_t* messages = row + randSharingSize;
      print_messages(messages);
    }
}


/**** Inits *************/


void init_rand(uint64_t* r){

  for(int i =0;i<randSharingSize;i++)
    r[i] =  i & 1;

}

/* This function  sets up the memory space for the execution of the prover 
   Space is allocated for all the views, states of parties, randomness is
   sampled and it is given back to OCAML.
   Randomness is already stored in the view space for all gates
   Randomness for input secret sharing is not
   The commitment keys are also stored at the end of the view 
   The global pointers to views are never used outside of this function,
   but we keep them for debugging.
   The global pointers for the states are just used when the initial
   inputs are consolidated into initial states after secret sharing,
   and then again in the commitment stage to put the initial inputs
   in the view.  */

  uint64_t * viewPP[5];
  uint64_t * statusPP[5];

CAMLprim value prover_rand_gen_c(value n_pinputs,value n_sinputs,value n_wires){
  CAMLparam4(n_pinputs, n_sinputs, n_sinputs, n_wires);
  CAMLlocal4(v,r_ss,r_mpc,r_cs);
  
  int n_wires_c = Int_val(n_wires);
  int n_pinputs_c = Int_val(n_pinputs);
  int n_sinputs_c = Int_val(n_sinputs);
  
  int total_inputs = n_pinputs_c + n_sinputs_c;
    
  printf("RAND nwires ninputs %d %d\n", n_wires_c, total_inputs);

  //---------------RANDOM SINPUTS-----------------------------
  // For each secret input we will require room for a secret sharing input/output.
  // This means a fresh randomness and a fresh sharing
  uint64_t* inRdPP = (uint64_t*) calloc ( n_sinputs_c * viewRowSize, sizeof(uint64_t));
 
  r_ss = caml_alloc(n_sinputs_c, 0);
  
  // for each secret input
  for(int ri = 0; ri < n_sinputs_c; ri++){
    // generate random
    uint64_t* inRdIndex = inRdPP + ri*viewRowSize;
    init_rand(inRdIndex); 
    Store_field(r_ss, ri, Val_long ((uintptr_t) inRdIndex));
  } 

  
  //--------------------------VIEW--------------------------------
  
  // for each party
  viewPP[0] = (uint64_t*) calloc(viewSize(n_wires_c), sizeof(uint64_t)  );
  viewPP[1] = (uint64_t*) calloc(viewSize(n_wires_c), sizeof(uint64_t)  );
  viewPP[2] = (uint64_t*) calloc(viewSize(n_wires_c), sizeof(uint64_t)  );
  viewPP[3] = (uint64_t*) calloc(viewSize(n_wires_c), sizeof(uint64_t)  );
  viewPP[4] = (uint64_t*) calloc(viewSize(n_wires_c), sizeof(uint64_t)  );

  statusPP[0] = (uint64_t*) calloc(stateSize(n_wires_c),sizeof(uint64_t));
  statusPP[1] = (uint64_t*) calloc(stateSize(n_wires_c),sizeof(uint64_t));
  statusPP[2] = (uint64_t*) calloc(stateSize(n_wires_c),sizeof(uint64_t));
  statusPP[3] = (uint64_t*) calloc(stateSize(n_wires_c),sizeof(uint64_t));
  statusPP[4] = (uint64_t*) calloc(stateSize(n_wires_c),sizeof(uint64_t));

  r_mpc = caml_alloc(nParties,0);

  for(int pi = 0; pi<nParties;pi++){
    
    uint64_t* viewParty = viewPP[pi];

    value r_mpc_id = caml_alloc(n_wires_c - total_inputs, 0);

    for(int wi = 0; wi < n_wires_c - total_inputs; wi++){
      uint64_t* viewWire = viewParty + (wi+total_inputs)*viewRowSize;
      init_rand(viewWire);
      Store_field(r_mpc_id, wi, Val_long ((uintptr_t)viewWire));
      
    }
    Store_field(r_mpc, pi, r_mpc_id); 
  }

  
  //----------------------------COMMITS --------------------------------

  r_cs = caml_alloc(nParties,0);
  
  for(int pi = 0; pi<nParties;pi++){
    Store_field(r_cs,pi,Val_long ((uintptr_t)(viewPP[pi]+viewSize(n_wires_c)-1)));
  }
  
  //------------------RETURN---------------------------------------------
  
  v = caml_alloc_tuple (3);
  Store_field(v, 0, r_ss);
  Store_field(v, 1, r_mpc);
  Store_field(v, 2, r_cs);
  
  CAMLreturn (v);
}


/* This function is called for each party to prepare the MPC initial state.
   It corresponds to the conversion from raw inputs to actual inputs.
   It puts public inputs and secret inputs in the initial state and returns
   back the pointer to the state. */
CAMLprim value initial_status_c (value pidv, value n_inputs, value inputs) {
  CAMLparam3(pidv, n_inputs, inputs);
  CAMLlocal1(v);

  printf("Entered initial status\n");

  int n_inputs_c = Int_val(n_inputs);

  int pid = Int_val(pidv);
  printf("Starting to fill status, pid = %d n_inputs_c = %d\n", pid, n_inputs_c);

  uint64_t* status=statusPP[pid];

  for (int i = 0; i < n_inputs_c; i++) {
     uintptr_t inp = Long_val(Field(inputs, i));
     uint64_t *share = (uint64_t *) inp;
    
     input_end5(share, status, i);
  }


  v = caml_alloc(2,0);
  Store_field(v, 0, Val_long(n_inputs_c));
  Store_field(v, 1, Val_long ((uintptr_t) status));
 
  CAMLreturn (v);
  
}

/**************** CALLS TO JASMIN ******************/


/* Takes as input the four words representing the secret and 
   the randomness for sharing (with accompanying space to
   gold the output secret sharings) returns an array of 5 
   pointers to the resulting shares. Note that secret sharing
   is  a call to start_input. */
CAMLprim value maurer_share_c(value rands, value pinp) {

  CAMLparam2(rands,pinp);
  CAMLlocal1(v);
  CAMLlocal5(v0,v1,v2,v3,v4);
  
  uint64_t input[rawShareSize];
  
  for(int k = 0; k < rawShareSize; k++)
      input[k] = Long_val (Field(pinp, k));
  
  uintptr_t aux = Long_val (rands);
  uint64_t *rands_c = (uint64_t *)aux;
 
  uint64_t *msgs_c = rands_c + randSharingSize;

  input_start5(input, msgs_c, rands_c);
  
  uint64_t * share0 = msgs_c + 0*shareSize;
  uint64_t * share1 = msgs_c + 1*shareSize;
  uint64_t * share2 = msgs_c + 2*shareSize;
  uint64_t * share3 = msgs_c + 3*shareSize;
  uint64_t * share4 = msgs_c + 4*shareSize;

  v0 = caml_alloc(2,0);
  Store_field(v0, 0, Val_int(0) );
  Store_field(v0, 1, Val_long ((uintptr_t) share0));
  
  v1 = caml_alloc(2,0);
  Store_field(v1, 0, Val_int(1) );
  Store_field(v1, 1, Val_long ((uintptr_t) share1));
    
  v2 = caml_alloc(2,0);
  Store_field(v2, 0, Val_int(2) );
  Store_field(v2, 1, Val_long ((uintptr_t) share2));
    
  v3 = caml_alloc(2,0);
  Store_field(v3, 0, Val_int(3) );
  Store_field(v3, 1, Val_long ((uintptr_t) share3));

  v4 = caml_alloc(2,0);
  Store_field(v4, 0, Val_int(4) );
  Store_field(v4, 1, Val_long ((uintptr_t) share4));
  
  v = caml_alloc(5,0);
  Store_field(v,0,v0);
  Store_field(v,1,v1);
  Store_field(v,2,v2);
  Store_field(v,3,v3);
  Store_field(v,4,v4);
  
  CAMLreturn (v);
}

/* The gates with no communication are simple calls to jasmin
   that get the pointer to the state and return the pointer
   to the state */
CAMLprim value maurer_add_c (value wl, value wr, value wst) {

  CAMLparam3(wl, wr, wst);
  CAMLlocal1(v);

  //printf("ADD GATE C\n");

  uint64_t wl_c = Int_val(wl);
  uint64_t wr_c = Int_val(wr);
  
  uint64_t wire_count_c = Int_val(Field(wst,0));
  
  uintptr_t aux = Long_val (Field(wst,1));
  uint64_t *status_c = (uint64_t *) aux;

  add5(status_c,wl_c,wr_c,wire_count_c);

  v = caml_alloc(2,0);
  Store_field(v, 0, Val_long(wire_count_c + 1));
  Store_field(v, 1, Val_long ((uintptr_t) status_c));
 
  CAMLreturn (v);
}

CAMLprim value maurer_smul_c (value wl, value wr, value wst) {
  CAMLparam3(wl, wr, wst);
  CAMLlocal1(v);

  //printf("SMUL GATE C\n");

  uint64_t wl_c = Int_val(wl);
  uint64_t wr_c = Int_val(wr);
  
  uint64_t wire_count_c = Int_val(Field(wst,0));
  
  uintptr_t aux = Long_val (Field(wst,1));
  uint64_t *status_c = (uint64_t *) aux;
  
  Smult5(status_c,wl_c,wr_c,wire_count_c);

  v = caml_alloc(2,0);
  Store_field(v, 0, Val_long(wire_count_c + 1));
  Store_field(v, 1, Val_long ((uintptr_t) status_c));
 
  CAMLreturn (v);
}

CAMLprim value maurer_const_c (value sec, value wst, value pid) {
  CAMLparam3(sec, wst,pid);
  CAMLlocal1(v);

  //printf("CONST GATE C\n");

  uint64_t wire_count_c = Int_val(Field(wst,0));
  
  uintptr_t aux = Long_val (Field(wst,1));
  uint64_t *status_c = (uint64_t *) aux;
  
  uint64_t pid_c = Int_val(pid);

  uint64_t input[rawShareSize];
    
  for(int k = 0; k < rawShareSize; k++)
      input[k] = Long_val (Field(sec, k));
    
  uint64_t msgs[sharingSize];

  const_start5(input, msgs);
    
  const_end5(msgs+pid_c*shareSize, status_c, wire_count_c);
    
  v = caml_alloc(2,0);
  Store_field(v, 0, Val_long(wire_count_c + 1));
  Store_field(v, 1, Val_long ((uintptr_t) status_c));

  CAMLreturn(v);
}

/* Multiplication returns the pointer to the first message, which is then
   extended to multiple messages in the OCaml wrapper. Maybe we can put
   everything here. It uses as message space the room we left next to the
   randomness in the view. The protocol orchestration calls dispatch to
   distribute the messages, in place, across the 5 views. Mul end is
   just a call to Jasmin. */
CAMLprim value maurer_mul_start_c (value wl, value wr, value wst, value r) {

  CAMLparam4(wl, wr, wst, r);
  CAMLlocal1(v);

  //printf("MUL START GATE C\n");

  uint64_t wl_c = Int_val(wl);
  uint64_t wr_c = Int_val(wr);
  
  uintptr_t aux = Long_val (Field(wst,1));
  uint64_t *status_c = (uint64_t *) aux;

  aux = Long_val (r);
  uint64_t *r_c = (uint64_t *) aux;

  mult_start5(status_c, wl_c, wr_c, r_c + randSharingSize, r_c);
  
  v = Val_long((uintptr_t)(r_c+randSharingSize));
  CAMLreturn (v);
}

CAMLprim value maurer_mul_end_c (value msgs, value wst) {
  CAMLparam2(msgs, wst);
  CAMLlocal1(v);

  //printf("MUL END GATE C\n");

  uint64_t wire_count_c = Int_val(Field(wst,0));
  
  uintptr_t aux = Long_val (Field(wst,1));
  uint64_t *status_c = (uint64_t *) aux;

  aux = Long_val (msgs);
  uint64_t *msgs_c = (uint64_t *) aux;

  mult_end5(msgs_c, status_c, wire_count_c);

  v = caml_alloc(2,0);
  Store_field(v, 0, Val_long(wire_count_c + 1));
  Store_field(v, 1, Val_long ((uintptr_t) status_c));

  CAMLreturn (v);
}

/* The final output generates messages, but we cannot put them
   directly in the view because we do not get a reference to the
   view via randomnesss. We therefore create fresh memory for this
   particular communication, which we return to OCaml to be stored
   as pointers in the view. Again the orchestrator will call 
   dispatch and output end just computes the unshare and
   returns the 4 integers that represent the secret. */
CAMLprim value maurer_output_start_c (value wid, value wst) {
  CAMLparam2(wid, wst);
  CAMLlocal1(v);

  uint64_t wid_c = Int_val(wid);
  
  uintptr_t aux = Long_val (Field(wst,1));
  uint64_t *status_c = (uint64_t *) aux;

  uint64_t * msgs = (uint64_t *) calloc(sharingSize, sizeof(uint64_t));
  
  out_start5(status_c, wid_c, msgs);

  v = Val_long((uintptr_t) msgs);
  CAMLreturn (v);
}

CAMLprim value maurer_output_end_c (value msgs) {
  CAMLparam1(msgs);
  CAMLlocal1(v);

  //printf("OUT END GATE C\n");

  uintptr_t aux = Long_val (msgs);
  uint64_t *msgs_c = (uint64_t *) aux;
  
  uint64_t output[rawShareSize];

  out_end5(msgs_c, output, -1);

  v = caml_alloc(4,0);
  for (int i = 0; i < rawShareSize; i++)
      Store_field(v, i, Val_long(output[i]));
  for (int i = rawShareSize; i < 4; i++)
      Store_field(v, i, Val_long(0));

  printf("C = %lld\n", output[0]);
  
  CAMLreturn(v);
}

/* Just a call to dispatch, which permutes the messages to into messages from */
CAMLprim value maurer_dispatch_c(value msgs0, value msgs1, value msgs2, value msgs3, value msgs4)
{
  
  CAMLparam5(msgs0, msgs1, msgs2, msgs3, msgs4);
  
  uintptr_t aux = Long_val (msgs0);
  uint64_t *msgs0_c = (uint64_t *)aux;
  aux = Long_val (msgs1);
  uint64_t *msgs1_c = (uint64_t *)aux;
  aux = Long_val (msgs2);
  uint64_t *msgs2_c = (uint64_t *)aux;
  aux = Long_val (msgs3);
  uint64_t *msgs3_c = (uint64_t *)aux;
  aux = Long_val (msgs4);
  uint64_t *msgs4_c = (uint64_t *)aux;

  dispatch(msgs0_c, msgs1_c, msgs2_c, msgs3_c, msgs4_c);
  
  CAMLreturn (Val_unit);
}

/* Compare two messages, i.e. if two shares are the same */
CAMLprim value compare_msg_c(value msgs0, value msgs1)
{
  
  CAMLparam2(msgs0, msgs1);
  CAMLlocal1(v);

  uintptr_t aux = Long_val (msgs0);
  uint64_t *msgs0_c = (uint64_t *)aux;
  aux = Long_val (msgs1);
  uint64_t *msgs1_c = (uint64_t *)aux;

  int res_c = memcmp(msgs0_c,msgs1_c,shareSize*sizeof(uint64_t));

  v = Val_bool(res_c ==0);
  CAMLreturn(v);

}
/***COMMITMENT GENERATION*****************/

extern unsigned char *shake128_alloc(const unsigned char *in,unsigned long long inlen);
#define hashsize 32

/* The prover commitment generation functions are performing an unverified optimization.
   We have set up things such that every part of the view is already in the
   same memory region. We just need to put the inputs there and the output
   messages. Once this is done, we call the hash */

/* pid, key address, number of inputs, number of randomnesses, last m is still not in view) 
external commitment_prover : int -> int -> int -> int -> int -> string = "commitment_prover_c" */

CAMLprim value commitment_prover_c(value pido, value keyaddr, value nins, value nrand, value lastm) {

  CAMLparam5(pido, keyaddr, nins, nrand, lastm);

  /* We get the key input, which gives us pointer to end of view */
  uintptr_t aux = Long_val (keyaddr);
  uint64_t *keyaddr_c = (uint64_t *)aux;

  int pid = Int_val(pido);

  /* We get the initial state, which gives us the number of inputs and the inputs */
  int ninputs = Int_val(nins);

  /* We get the number of randomnesses */
  int nrand_c = Int_val(nrand);

  int wire_count_c = nrand_c+ninputs;

  /* We can now compute the view base and set the inputs in the view */ 
  uint64_t *view_base = keyaddr_c-(viewSize(wire_count_c)-1);

  /* The inputs are not in the view yet, so we need to put them there.
     We take advantage that they are in the state of the party, rather
     then getting them again in raw form and encoding them again */
  for(int i = 0; i < ninputs; i++) {
    memcpy(view_base+i*viewRowSize+randSharingSize,statusPP[pid]+i*stateRowSize,shareSize*sizeof(uint64_t));
  }

  /* Now we need to get the last message and also put it in the view */
  aux = Long_val (lastm);
  uint64_t *lastim_c = (uint64_t *)aux;

  memcpy(view_base+wire_count_c*viewRowSize+randSharingSize,lastim_c,sharingSize*sizeof(uint64_t)); /*put outputs */

  unsigned char *hash =  shake128_alloc((unsigned char*)view_base,viewSize(wire_count_c)*8); /* some extra rubish goes in */

  char buffer[12];
  sprintf(buffer, "commit%d.dat", pid);

 FILE *out = fopen(buffer, "wb");
  if(out != NULL)
  {
    size_t to_go = hashsize;
    while(to_go > 0)
    {
      const size_t wrote = fwrite(hash, 1, to_go, out);
      if(wrote == 0)
        break;
      to_go -= wrote;
    }
    fclose(out);
  }
   
  CAMLreturn (Val_unit);
}

/* The verifier commitment generation functions are performing an unverified optimization.
   We have set up things such that every part of the view is already in the
   same memory region. We simply call the hash */

CAMLprim value commitment_verifier_c(value pido, value keyaddr, value nins, value nrand, value hash) {
  CAMLparam5(pido, keyaddr, nins, nrand,hash);
  CAMLlocal1(v);

  /* We get the pid */
  int pid = Int_val(pido);

  /* We get the key input, which gives us pointer to end of view */
  uintptr_t aux = Long_val (keyaddr);
  uint64_t *keyaddr_c = (uint64_t *)aux;

  /* We get the initial state, which gives us the number of inputs and the inputs */
  int ninputs = Int_val(nins);

  /* We get the number of randomnesses */
  int nrand_c = Int_val(nrand);

  int wire_count_c = nrand_c+ninputs;

  /* We can now compute the view base */ 
  uint64_t *view_base = keyaddr_c-(viewSize(wire_count_c)-1);

  unsigned char *hashnew =  shake128_alloc((unsigned char*)view_base,viewSize(wire_count_c)*8); /* some extra rubish goes in */

  char buffer[12];
  sprintf(buffer, "commit%d.dat", pid);

  int res_c = 0;
  FILE *in = fopen(buffer, "rb");
  if(in != NULL) {

    fseek(in, 0, SEEK_END);
    long fsize = ftell(in);
    fseek(in, 0, SEEK_SET);  /* same as rewind(f); */
    if (fsize == hashsize) {
       uint64_t *hash_c = malloc(fsize);
       fread(hash_c, 1, fsize, in);
       fclose(in);
       res_c = memcmp(hash_c,hashnew,hashsize);
    }
  }
  v = Val_bool(res_c ==0);
  CAMLreturn(v);
}

CAMLprim value write_opening(value pido, value npins, value nsins, value nrand) {
  //printf("WRITE VIEW START!!! \n");

  CAMLparam4(pido, npins, nsins, nrand);

  /* We get the number of inputs (*they are already in the view *) */
  int npins_c = Int_val(npins);
  int nsins_c = Int_val(nsins);
  int ninputs = npins_c + nsins_c;

  /* We get the pid */
  int pid = Int_val(pido);

  /* We get the number of randomnesses */
  int nrand_c = Int_val(nrand);

  int wire_count_c = nrand_c+ninputs;

  printf("Write pid %d nrand %d nwires %d\n",pid, nrand_c,wire_count_c );

  uint64_t *view_base = viewPP[pid];

  char buffer[12];
  sprintf(buffer, "view%d.dat", pid);

 FILE *out = fopen(buffer, "wb");
  if(out != NULL)
  {
    size_t to_go = viewSize(wire_count_c)*sizeof(uint64_t);
    while(to_go > 0)
    {
      const size_t wrote = fwrite(view_base, 1, to_go, out);
      if(wrote == 0)
        break;
      to_go -= wrote;
    }
    fclose(out);
  }
   
  CAMLreturn (Val_unit);
}


/* This function is setting up the verifier workspace for the final check based
 on the two views opened by the prover. The verifier gets two large memory
 regions; one is intended as a read-only version of the opened views (which the
 OCaml gets as a bunch of pointers). The second one is supposed to contain 
 the randomnesses and room for evaluating the protocol.
 We allocate the state of the party, so that it can be used again. */

/* pid, number of pinputs, number of sinputs number of randomnesses) */

CAMLprim value read_opening(value pido, value npins, value nsins, value nrand) {
  //printf("COPY VIEW START!!! \n");

  CAMLparam4(pido, npins, nsins, nrand);
  CAMLlocal4(v,sins_ret,rand_ret,msgs_ret);

  /* We get the number of inputs (*they are already in the view *) */
  int npins_c = Int_val(npins);
  int nsins_c = Int_val(nsins);
  int ninputs = npins_c + nsins_c;

  /* We get the pid */
  int pid = Int_val(pido);

  /* We get the number of randomnesses */
  int nrand_c = Int_val(nrand);

  int wire_count_c = nrand_c+ninputs;

  printf("Read pid %d nrand %d nwires %d\n",pid, nrand_c,wire_count_c );


  char buffer[12];
  sprintf(buffer, "view%d.dat", pid);

  uint64_t *view_new_rands;
  FILE *in = fopen(buffer, "rb");
  if(in != NULL) {

    fseek(in, 0, SEEK_END);
    long fsize = ftell(in);
    fseek(in, 0, SEEK_SET);  /* same as rewind(f); */
    if (fsize == viewSize(wire_count_c)*sizeof(uint64_t)) {
        /* This will be used to recompute the gates on the verifier side */
        view_new_rands = (uint64_t*) calloc(viewSize(wire_count_c),sizeof(uint64_t));
       fread(view_new_rands, 1, fsize, in);
       fclose(in);

    }
    else { exit(-1);}
  }
  else { exit(-1);}

  /* This will be used to compare the messages and compute the commitments on the verifier side */
  uint64_t *view_new_msgs = (uint64_t*) calloc(viewSize(wire_count_c),sizeof(uint64_t));
  /* input shares new: we reconstruct a shared input from the shares in the view */
  uint64_t *isharesnew = (uint64_t*) calloc(stateSize(nsins_c),sizeof(uint64_t));

  memcpy(view_new_msgs,view_new_rands,viewSize(wire_count_c)*sizeof(uint64_t));
  for (int k=0; k < nsins_c; k++) {
     memcpy(isharesnew+shareSize*k,view_new_rands+viewRowSize*npins_c+viewRowSize*k+randSharingSize,shareSize*sizeof(uint64_t));
  }

  sins_ret=caml_alloc(nsins_c,0);
  for (int i = 0; i < nsins_c; i++) {
    Store_field(sins_ret,i,Val_long ((uintptr_t)(isharesnew+i*stateRowSize)));
  }

  rand_ret=caml_alloc(nrand_c,0);
  for (int i = 0; i < nrand_c; i++) {
    Store_field(rand_ret,i,Val_long ((uintptr_t)(view_new_rands+(i+ninputs)*viewRowSize)));
  }
  msgs_ret=caml_alloc(nrand_c+1,0);
  for (int i = 0; i < nrand_c+1; i++) {
    Store_field(msgs_ret,i,Val_long ((uintptr_t)(view_new_msgs+(i+ninputs)*viewRowSize+randSharingSize)));
  }

  /* CREATE SPACE FOR THE VERIFIER'S VIEW OF THE PARTY STATE (init_status will use this) */
  statusPP[pid]=(uint64_t*) calloc(stateSize(wire_count_c),sizeof(uint64_t));

  v = caml_alloc(4,0);
  Store_field(v, 0, Val_long ((uintptr_t)(view_new_msgs+(wire_count_c+1)*viewRowSize)));
  Store_field(v, 1, sins_ret);
  Store_field(v, 2, rand_ret);
  Store_field(v, 3, msgs_ret);
  CAMLreturn (v);
}

/* val -> shrs */
CAMLprim value maurer_pshare_c (value pinp) {
  CAMLparam1(pinp);
  CAMLlocal1(v);

  uint64_t input[rawShareSize];
  
  for(int k = 0; k < rawShareSize; k++)
      input[k] = Long_val (Field(pinp, k));

  uint64_t * msgs = (uint64_t *) calloc (sharingSize, sizeof(uint64_t));

  const_start5(input, msgs);

  v = caml_alloc(5,0);
  for (int i = 0; i < 5; i++)
     Store_field(v, i, Val_long((uintptr_t) (msgs+i*shareSize)));
  
  CAMLreturn(v);
}

//external maurer_punshare : int -> int Array.t = "maurer_punshare"
CAMLprim value maurer_punshare_c(value s) {
  CAMLparam1(s);
  CAMLlocal1(v);

  uintptr_t aux = Long_val (s);
  uint64_t *sp = (uint64_t *)aux;

  v = caml_alloc(4,0);
  for (int i = 0; i < rawShareSize; i++)
      Store_field(v, i, Val_long(sp[i]));
  for (int i = rawShareSize; i < 4; i++)
      Store_field(v, i, Val_long(0));

  CAMLreturn (v);
}

//external maurer_rawshare : int -> int -> int Array.t = "maurer_rawshare_c"
CAMLprim value maurer_rawshare_c(value s, value i) {
  CAMLparam2(s,i);
  CAMLlocal1(v);


  uintptr_t aux = Long_val (s);
  uint64_t *sp = (uint64_t *)aux;

  uint64_t i_c = Long_val (i);

  /* printf ("maurer_rawshare_c %lld %d\n", sp, i_c); */

  v = caml_alloc(4,0);
  for (int k = 0; k < rawShareSize; k++)
      Store_field(v, k, Val_long(sp[k+rawShareSize*i_c]));
  for (int k = rawShareSize; k < 4; k++)
      Store_field(v, k, Val_long(0));
  CAMLreturn (v);
}


//external maurer_reconstruct : (Z.t * nativeint) list -> Z.t = "maurer_reconstruct_c"
CAMLprim value maurer_reconstruct_c(value ss) {
  printf ("maurer_reconstruct_c THIS SHOULD NOT BE USED in MitH\n");
  exit(-1);
  CAMLparam1(ss);
  CAMLlocal1(v);
  CAMLreturn (v);
}




