#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include "emulator.h"
#include "gbn.h"
#include "sr.h"
/* ******************************************************************
   Go Back N protocol.  Adapted from J.F.Kurose
   ALTERNATING BIT AND GO-BACK-N NETWORK EMULATOR: VERSION 1.2
   Network properties:
   - one way network delay averages five time units (longer if there
   are other messages in the channel for GBN), but can be larger
   - packets can be corrupted (either the header or the data portion)
   or lost, according to user-defined probabilities
   - packets will be delivered in the order in which they were sent
   (although some can be lost).

   Modifications:
   - removed bidirectional GBN code and other code not used by prac.
   - fixed C style to adhere to current programming style
   - added GBN implementation
**********************************************************************/

#define RTT  16.0       /* round trip time.  MUST BE SET TO 16.0 when submitting assignment */
#define WINDOWSIZE 6    /* the maximum number of buffered unacked packet
                          MUST BE SET TO 6 when submitting assignment */
#define SEQSPACE 64      /* the min sequence space for GBN must be at least windowsize + 1 */
#define NOTINUSE (-1)   /* used to fill header fields that are not being used */

/* generic procedure to compute the checksum of a packet.  Used by both sender and receiver
   the simulator will overwrite part of your packet with 'z's.  It will not overwrite your
   original checksum.  This procedure must generate a different checksum to the original if
   the packet is corrupted.
*/
int ComputeChecksum(struct pkt packet)
{
  int checksum = 0;
  int i;

  checksum = packet.seqnum;
  checksum += packet.acknum;
  for ( i=0; i<20; i++ )
    checksum += (int)(packet.payload[i]);

  return checksum;
}

bool IsCorrupted(struct pkt packet)
{
  if (packet.checksum == ComputeChecksum(packet))
    return (false);
  else
    return (true);
}


/********* Sender (A) variables and functions ************/

enum PacketStatus {
  NOT_SENT,
  SENT_NOT_ACKED,
  ACKED
};

static struct pkt buffer[SEQSPACE];
static enum PacketStatus status[SEQSPACE];
static int base = 0;   
static bool timer_running[SEQSPACE];              
static int nextseqnum = 0;   
static struct pkt B_buffer[SEQSPACE];
static int B_received[SEQSPACE];  
static int B_base = 0;

/* called from layer 5 (application layer), passed the message to be sent to other side */
void A_output(struct msg message)
{
  struct pkt sendpkt;
  int i;

  /* if not blocked waiting on ACK */
  if ((nextseqnum + SEQSPACE - base) % SEQSPACE < WINDOWSIZE) {
    if (TRACE > 1)
      printf("----A: New message arrives, send window is not full, send new messge to layer3!\n");

    /* create packet */
    sendpkt.seqnum = nextseqnum;
    sendpkt.acknum = NOTINUSE;
    for ( i=0; i<20 ; i++ )
      sendpkt.payload[i] = message.data[i];
    sendpkt.checksum = ComputeChecksum(sendpkt);

    /* put packet in window buffer */
    /* windowlast will always be 0 for alternating bit; but not for GoBackN */
    buffer[nextseqnum] = sendpkt;
    status[nextseqnum] = SENT_NOT_ACKED;


    /* send out packet */
    if (TRACE > 0)
      printf("Sending packet %d to layer 3\n", sendpkt.seqnum);
    tolayer3 (A, sendpkt);
	if (!timer_running[nextseqnum]) {
    timer_running[nextseqnum] = true;
    
	}
	starttimer(A, RTT);
    nextseqnum = (nextseqnum + 1) % SEQSPACE;
  }else {
    if (TRACE > 0)
      printf("----A: New message arrives, send window is full\n");
    window_full++;
  }
}


/* called from layer 3, when a packet arrives for layer 4
   In this practical this will always be an ACK as B never sends data.
*/
void A_input(struct pkt packet)
{
   int acknum;
   int has_unacked;
   int i;
   acknum = packet.acknum;
   if (packet.checksum != ComputeChecksum(packet)) {
    if (TRACE > 0)
      printf("----A: uncorrupted ACK %d is received\n",packet.acknum);
    return;
  }
  
  status[acknum] = ACKED;
  timer_running[acknum] = false;
   
  if (TRACE > 0)
    printf("----A: ACK %d is not a duplicate\n",packet.acknum);

  if ((acknum < base && base - acknum > SEQSPACE / 2) ||  
      (acknum >= base && acknum < (base + WINDOWSIZE) % SEQSPACE)) {

 
    status[acknum] = ACKED;

    if (TRACE > 0)
      printf("----A: ACK %d is within window and marked as ACKED.\n", acknum);
    
	has_unacked = 0;
  
	while (status[base] == ACKED) {
      if (TRACE > 0)
        printf("----A: Sliding window, base %d -> %d\n", base, (base + 1) % SEQSPACE);
      status[base] = NOT_SENT;
      base = (base + 1) % SEQSPACE;
    }
	
	
    for (i = 0; i < WINDOWSIZE; i++) {
      int idx = (base + i) % SEQSPACE;
      if (status[idx] == SENT_NOT_ACKED) {
        has_unacked = 1;
        break;
    }
}

if (!has_unacked) {
  if (TRACE > 0)
    printf("----A: duplicate ACK received, do nothing!\n");
  stoptimer(A);
}
  } else {
    if (TRACE > 0)
      printf("----A: corrupted ACK is received, do nothing!\n");
  }
}

/* called when A's timer goes off */
void A_timerinterrupt(void)
{
  int i;
  for (i = 0; i < WINDOWSIZE; i++) {
    int idx = (base + i) % SEQSPACE;
    if (status[idx] == SENT_NOT_ACKED) {
      tolayer3(A, buffer[idx]);
      if (TRACE > 0)
        printf("----A: Timeout, resent packet %d\n", buffer[idx].seqnum);
    }
  }

  
  starttimer(A, 1.0);
}




void A_init(void)
{
  int i;
  base = 0;
  nextseqnum = 0;

  for (i = 0; i < SEQSPACE; i++) {
	  timer_running[i] = false;
      status[i] = NOT_SENT;
  }
  
  starttimer(A, 1.0);

  if (TRACE > 0)
    printf("----A: Sender initialized.\n");
}



/********* Receiver (B)  variables and procedures ************/



/* called from layer 3, when a packet arrives for layer 4 at B*/
void B_input(struct pkt packet)
{
	int seq;
	struct pkt ackpkt;
	int i;
   if (packet.checksum != ComputeChecksum(packet)) {
    if (TRACE > 0)
      printf("----B: packet %d is correctly received, send ACK!\n",packet.seqnum);
    return;
  }

  seq = packet.seqnum;

  if ((seq < B_base && B_base - seq > SEQSPACE / 2) ||
      (seq >= B_base && seq < (B_base + WINDOWSIZE) % SEQSPACE)) {

    if (TRACE > 0)
      printf("----B: Packet %d within receive window.\n", seq);

    if (B_received[seq] == 0) {
      B_buffer[seq] = packet;
      B_received[seq] = 1;
      if (TRACE > 0)
        printf("----B: Cached packet %d\n", seq);
    } else {
      if (TRACE > 0)
        printf("----B: Duplicate packet %d, already cached.\n", seq);
    }

    
    ackpkt.seqnum = 0;
    ackpkt.acknum = seq;
	
    for (i = 0; i < 20; i++) ackpkt.payload[i] = 0;
    ackpkt.checksum = ComputeChecksum(ackpkt);
    tolayer3(B, ackpkt);

    if (TRACE > 0)
      printf("----B: Sent ACK %d\n", ackpkt.acknum);
    while (B_received[B_base] == 1) {
      if (TRACE > 0)
        printf("----B: Delivering packet %d to layer 5\n", B_base);
      tolayer5(B, B_buffer[B_base].payload);
      B_received[B_base] = 0;
      B_base = (B_base + 1) % SEQSPACE;
    }
  
  } else {
    if (TRACE > 0)
      printf("----B: Packet %d outside receive window, ignored.\n", seq);
  }
}

/* the following routine will be called once (only) before any other */
/* entity B routines are called. You can use it to do any initialization */
void B_init(void)
{
  int i;
  B_base = 0;
  
  for (i = 0; i < SEQSPACE; i++) {
    B_received[i] = 0;
  }

  if (TRACE > 0)
    printf("----B: Receiver initialized.\n");
}

/******************************************************************************
 * The following functions need be completed only for bi-directional messages *
 *****************************************************************************/

/* Note that with simplex transfer from a-to-B, there is no B_output() */
void B_output(struct msg message)
{
}

/* called when B's timer goes off */
void B_timerinterrupt(void)
{
}
