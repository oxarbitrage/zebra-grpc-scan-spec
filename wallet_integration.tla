------------------------- MODULE wallet_integration -------------------------
(***************************************************************************)
(* The memory wallet integration with zebra specification.                 *)
(* The specs simulates a call to the create_account grpc method as a       *)
(* starting point and then the grpc method calls the create_account        *)
(* procedure in the zcash_client_backend side. The grpc method then sends  *)
(* the key to the memory wallet and the memory wallet adds the key to the  *)
(* accounts set. The memory wallet then sends a block to the memory wallet *)
(* and the memory wallet adds the block to the blocks set.                 *)
(*                                                                         *)
(* The memory wallet is a simple algorithm that listens for requests and   *)
(* sends adding requests to the scan task. The scan task listens for       *)
(* requests from the services process and adds tasks to the scan task set. *)
(* The scan task also adds account to the memory wallet and either sends   *)
(* "scanned" blocks to the memory wallet or does nothing more.             *)
(*                                                                         *)
(* The main process is the entry point of the model and calls the          *)
(* create_account grpc method.                                             *)
(*                                                                         *)
(***************************************************************************)
EXTENDS TLC, Integers, Sequences, Json, FiniteSets

StatusWaiting == "waiting"
StatusAdding == "adding"
CreateAccountServiceRequest == "create_account"

(*--algorithm wallet_integration

variables
    \* A string that will be used as a response to any of the gRPC method calls, initially empty.
    response = "";
    \* The current service request flag, initially listening for requests.
    service_request = StatusWaiting;
    \* The current status of the scan task, initially listening for requests.
    scan_task_status = StatusWaiting;
    \* The set of scan tasks that are currently being processed.
    scan_tasks = {};
    \* The key that will be served to the client after a create account request.
    key_to_be_served = "";
    \* The block that will be served to the client after a scan task finds a relevant block, initially empty.
    block_to_be_served = [height |-> 0, hash |-> "000000"];
    \* The accounts that are currently being processed, initially empty.
    accounts = <<[account_id |-> 0, ufvk |-> ""]>>;
    \* The blocks that are currently being processed, initially empty.
    blocks = <<>>;

\* UTILITY PROCEDURES:

\* The `create_account` grpc method.
procedure create_account_grpc()
begin
    CreateAccountGrpc:
        service_request := CreateAccountServiceRequest;
end procedure;

\* The `create_account` in the zcash_client_backend side.
procedure create_account_zcash_client_backend()
begin
    CreateAccountZcashClientBackend:
        response := "zxviews...";
        return;
end procedure;

\* The `put_block` in the zcash_client_backend side.
procedure put_block_zcash_client_backend()
begin
    PutBlockZcashClientBackend:
        blocks := Append(blocks, block_to_be_served);
end procedure;

\* SERVICES PROCESS:

\* Listen for requests and send adding requests to scan task.
process services = "SERVICES"
begin
    Services:
        \* We only have one service request in this algorithm.
        if service_request = CreateAccountServiceRequest then
            CreateAccount:
                scan_task_status := StatusAdding;
            CallZcashClientBackend:
                call create_account_zcash_client_backend();
            SendKey:
                key_to_be_served := response;
        end if;
    ServicesLoop:
        goto Services;
end process;


\* SCAN TASK PROCESS:

(* Listen for requests from the services process and:
- Add tasks to the scan task set.
- Add account to the memory wallet.
- Either send "scanned" blocks to the memory wallet or do nothing more.
*)
process scantask = "SCAN TASK"
variables inner_state = {}, inner_accounts = <<>>, inner_blocks = <<>>;
begin
    GetScanTasks:
        inner_state := scan_tasks;
    GetAccounts:
        inner_accounts := accounts;
    GetBlocks:
        inner_blocks := blocks;
    ScanTask:
        if scan_task_status = StatusAdding then
            AddingAccount:          
                accounts := Append(inner_accounts, [account_id |-> inner_accounts[Len(inner_accounts)].account_id + 1, ufvk |-> key_to_be_served]);
                inner_state := inner_state \union {key_to_be_served};    
                scan_task_status := StatusWaiting;
        end if;
    SendBlock:
        either
            block_to_be_served := [height |-> 1, hash |-> "111111"];
            call put_block_zcash_client_backend();
        or
            skip;
        end either;
    ScanTaskLoop:
        goto ScanTask;
end process;

\* MAIN PROCESS:

process Main = "MAIN"
begin
    CreteAccountCall:
        \* The grpc is the entry point of the model.
        call create_account_grpc();
    End:
        skip;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "2e1ecc63" /\ chksum(tla) = "d770e1ae")
VARIABLES response, service_request, scan_task_status, scan_tasks, 
          key_to_be_served, block_to_be_served, accounts, blocks, pc, stack, 
          inner_state, inner_accounts, inner_blocks

vars == << response, service_request, scan_task_status, scan_tasks, 
           key_to_be_served, block_to_be_served, accounts, blocks, pc, stack, 
           inner_state, inner_accounts, inner_blocks >>

ProcSet == {"SERVICES"} \cup {"SCAN TASK"} \cup {"MAIN"}

Init == (* Global variables *)
        /\ response = ""
        /\ service_request = StatusWaiting
        /\ scan_task_status = StatusWaiting
        /\ scan_tasks = {}
        /\ key_to_be_served = ""
        /\ block_to_be_served = [height |-> 0, hash |-> "000000"]
        /\ accounts = <<[account_id |-> 0, ufvk |-> ""]>>
        /\ blocks = <<>>
        (* Process scantask *)
        /\ inner_state = {}
        /\ inner_accounts = <<>>
        /\ inner_blocks = <<>>
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "SERVICES" -> "Services"
                                        [] self = "SCAN TASK" -> "GetScanTasks"
                                        [] self = "MAIN" -> "CreteAccountCall"]

CreateAccountGrpc(self) == /\ pc[self] = "CreateAccountGrpc"
                           /\ service_request' = CreateAccountServiceRequest
                           /\ pc' = [pc EXCEPT ![self] = "Error"]
                           /\ UNCHANGED << response, scan_task_status, 
                                           scan_tasks, key_to_be_served, 
                                           block_to_be_served, accounts, 
                                           blocks, stack, inner_state, 
                                           inner_accounts, inner_blocks >>

create_account_grpc(self) == CreateAccountGrpc(self)

CreateAccountZcashClientBackend(self) == /\ pc[self] = "CreateAccountZcashClientBackend"
                                         /\ response' = "zxviews..."
                                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                         /\ UNCHANGED << service_request, 
                                                         scan_task_status, 
                                                         scan_tasks, 
                                                         key_to_be_served, 
                                                         block_to_be_served, 
                                                         accounts, blocks, 
                                                         inner_state, 
                                                         inner_accounts, 
                                                         inner_blocks >>

create_account_zcash_client_backend(self) == CreateAccountZcashClientBackend(self)

PutBlockZcashClientBackend(self) == /\ pc[self] = "PutBlockZcashClientBackend"
                                    /\ blocks' = Append(blocks, block_to_be_served)
                                    /\ pc' = [pc EXCEPT ![self] = "Error"]
                                    /\ UNCHANGED << response, service_request, 
                                                    scan_task_status, 
                                                    scan_tasks, 
                                                    key_to_be_served, 
                                                    block_to_be_served, 
                                                    accounts, stack, 
                                                    inner_state, 
                                                    inner_accounts, 
                                                    inner_blocks >>

put_block_zcash_client_backend(self) == PutBlockZcashClientBackend(self)

Services == /\ pc["SERVICES"] = "Services"
            /\ IF service_request = CreateAccountServiceRequest
                  THEN /\ pc' = [pc EXCEPT !["SERVICES"] = "CreateAccount"]
                  ELSE /\ pc' = [pc EXCEPT !["SERVICES"] = "ServicesLoop"]
            /\ UNCHANGED << response, service_request, scan_task_status, 
                            scan_tasks, key_to_be_served, block_to_be_served, 
                            accounts, blocks, stack, inner_state, 
                            inner_accounts, inner_blocks >>

CreateAccount == /\ pc["SERVICES"] = "CreateAccount"
                 /\ scan_task_status' = StatusAdding
                 /\ pc' = [pc EXCEPT !["SERVICES"] = "CallZcashClientBackend"]
                 /\ UNCHANGED << response, service_request, scan_tasks, 
                                 key_to_be_served, block_to_be_served, 
                                 accounts, blocks, stack, inner_state, 
                                 inner_accounts, inner_blocks >>

CallZcashClientBackend == /\ pc["SERVICES"] = "CallZcashClientBackend"
                          /\ stack' = [stack EXCEPT !["SERVICES"] = << [ procedure |->  "create_account_zcash_client_backend",
                                                                         pc        |->  "SendKey" ] >>
                                                                     \o stack["SERVICES"]]
                          /\ pc' = [pc EXCEPT !["SERVICES"] = "CreateAccountZcashClientBackend"]
                          /\ UNCHANGED << response, service_request, 
                                          scan_task_status, scan_tasks, 
                                          key_to_be_served, block_to_be_served, 
                                          accounts, blocks, inner_state, 
                                          inner_accounts, inner_blocks >>

SendKey == /\ pc["SERVICES"] = "SendKey"
           /\ key_to_be_served' = response
           /\ pc' = [pc EXCEPT !["SERVICES"] = "ServicesLoop"]
           /\ UNCHANGED << response, service_request, scan_task_status, 
                           scan_tasks, block_to_be_served, accounts, blocks, 
                           stack, inner_state, inner_accounts, inner_blocks >>

ServicesLoop == /\ pc["SERVICES"] = "ServicesLoop"
                /\ pc' = [pc EXCEPT !["SERVICES"] = "Services"]
                /\ UNCHANGED << response, service_request, scan_task_status, 
                                scan_tasks, key_to_be_served, 
                                block_to_be_served, accounts, blocks, stack, 
                                inner_state, inner_accounts, inner_blocks >>

services == Services \/ CreateAccount \/ CallZcashClientBackend \/ SendKey
               \/ ServicesLoop

GetScanTasks == /\ pc["SCAN TASK"] = "GetScanTasks"
                /\ inner_state' = scan_tasks
                /\ pc' = [pc EXCEPT !["SCAN TASK"] = "GetAccounts"]
                /\ UNCHANGED << response, service_request, scan_task_status, 
                                scan_tasks, key_to_be_served, 
                                block_to_be_served, accounts, blocks, stack, 
                                inner_accounts, inner_blocks >>

GetAccounts == /\ pc["SCAN TASK"] = "GetAccounts"
               /\ inner_accounts' = accounts
               /\ pc' = [pc EXCEPT !["SCAN TASK"] = "GetBlocks"]
               /\ UNCHANGED << response, service_request, scan_task_status, 
                               scan_tasks, key_to_be_served, 
                               block_to_be_served, accounts, blocks, stack, 
                               inner_state, inner_blocks >>

GetBlocks == /\ pc["SCAN TASK"] = "GetBlocks"
             /\ inner_blocks' = blocks
             /\ pc' = [pc EXCEPT !["SCAN TASK"] = "ScanTask"]
             /\ UNCHANGED << response, service_request, scan_task_status, 
                             scan_tasks, key_to_be_served, block_to_be_served, 
                             accounts, blocks, stack, inner_state, 
                             inner_accounts >>

ScanTask == /\ pc["SCAN TASK"] = "ScanTask"
            /\ IF scan_task_status = StatusAdding
                  THEN /\ pc' = [pc EXCEPT !["SCAN TASK"] = "AddingAccount"]
                  ELSE /\ pc' = [pc EXCEPT !["SCAN TASK"] = "SendBlock"]
            /\ UNCHANGED << response, service_request, scan_task_status, 
                            scan_tasks, key_to_be_served, block_to_be_served, 
                            accounts, blocks, stack, inner_state, 
                            inner_accounts, inner_blocks >>

AddingAccount == /\ pc["SCAN TASK"] = "AddingAccount"
                 /\ accounts' = Append(inner_accounts, [account_id |-> inner_accounts[Len(inner_accounts)].account_id + 1, ufvk |-> key_to_be_served])
                 /\ inner_state' = (inner_state \union {key_to_be_served})
                 /\ scan_task_status' = StatusWaiting
                 /\ pc' = [pc EXCEPT !["SCAN TASK"] = "SendBlock"]
                 /\ UNCHANGED << response, service_request, scan_tasks, 
                                 key_to_be_served, block_to_be_served, blocks, 
                                 stack, inner_accounts, inner_blocks >>

SendBlock == /\ pc["SCAN TASK"] = "SendBlock"
             /\ \/ /\ block_to_be_served' = [height |-> 1, hash |-> "111111"]
                   /\ stack' = [stack EXCEPT !["SCAN TASK"] = << [ procedure |->  "put_block_zcash_client_backend",
                                                                   pc        |->  "ScanTaskLoop" ] >>
                                                               \o stack["SCAN TASK"]]
                   /\ pc' = [pc EXCEPT !["SCAN TASK"] = "PutBlockZcashClientBackend"]
                \/ /\ TRUE
                   /\ pc' = [pc EXCEPT !["SCAN TASK"] = "ScanTaskLoop"]
                   /\ UNCHANGED <<block_to_be_served, stack>>
             /\ UNCHANGED << response, service_request, scan_task_status, 
                             scan_tasks, key_to_be_served, accounts, blocks, 
                             inner_state, inner_accounts, inner_blocks >>

ScanTaskLoop == /\ pc["SCAN TASK"] = "ScanTaskLoop"
                /\ pc' = [pc EXCEPT !["SCAN TASK"] = "ScanTask"]
                /\ UNCHANGED << response, service_request, scan_task_status, 
                                scan_tasks, key_to_be_served, 
                                block_to_be_served, accounts, blocks, stack, 
                                inner_state, inner_accounts, inner_blocks >>

scantask == GetScanTasks \/ GetAccounts \/ GetBlocks \/ ScanTask
               \/ AddingAccount \/ SendBlock \/ ScanTaskLoop

CreteAccountCall == /\ pc["MAIN"] = "CreteAccountCall"
                    /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "create_account_grpc",
                                                               pc        |->  "End" ] >>
                                                           \o stack["MAIN"]]
                    /\ pc' = [pc EXCEPT !["MAIN"] = "CreateAccountGrpc"]
                    /\ UNCHANGED << response, service_request, 
                                    scan_task_status, scan_tasks, 
                                    key_to_be_served, block_to_be_served, 
                                    accounts, blocks, inner_state, 
                                    inner_accounts, inner_blocks >>

End == /\ pc["MAIN"] = "End"
       /\ TRUE
       /\ pc' = [pc EXCEPT !["MAIN"] = "Done"]
       /\ UNCHANGED << response, service_request, scan_task_status, scan_tasks, 
                       key_to_be_served, block_to_be_served, accounts, blocks, 
                       stack, inner_state, inner_accounts, inner_blocks >>

Main == CreteAccountCall \/ End

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == services \/ scantask \/ Main
           \/ (\E self \in ProcSet:  \/ create_account_grpc(self)
                                     \/ create_account_zcash_client_backend(self)
                                     \/ put_block_zcash_client_backend(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=============================================================================
