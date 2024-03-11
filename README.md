# The Zebra GRPC Scanner Spefification

## Introduction

The [Zebra](https://github.com/ZcashFoundation/zebra) project has recently developed an MVP for a gRPC interface that interacts with the `zebra-scanner` crate functionality. This document serves as a comprehensive specification for the Zebra gRPC scanner functionality. It outlines the motivation behind the development, presents the design diagram used during the design stage, and provides a formal specification of the system.

## Motivation

The motivation behind developing the Zebra gRPC scanner functionality was to enhance interoperability and accessibility to `zebra-scanner`s core features. By providing a gRPC interface, we aim to simplify integration with other systems and improve overall usability.

## Design Diagram

The design diagram (v0.6) illustrates the various components and interactions within the Zebra gRPC scanner system. It outlines the flow of requests and responses between different modules and services. Each node in the diagram represents a specific function or service, while the arrows denote the flow of data or control between them.

```mermaid
flowchart TD
    zebra-scan([zebra-scan]) --> |Service|requests/responses(Requests / Responses\n#8182)
    zebra-node-services([zebra-node-services]) ---> |Request and response type signatures|requests/responses(Requests / Responses\n#8182)
    requests/responses ---> |Service call|info[(Info\n#8162)]
    requests/responses ---> |Service call|results[(Results\n#8205)]
    requests/responses ---> |Service call|register[(Register\n#8203)]
    requests/responses ---> |Service call|delete[(Delete\n#8204)]
    requests/responses ---> |Service call|clear[(Clear\n#8207)]
    requests/responses ---> |Service call|subscribe[(Subscribe\n#8206)]
    requests/responses ---> |Service call|status[(Status\n#8257)]
    
    getinfo(getinfo) ----> |gRPC method|zebra-grpc
    info ----> getinfo(getinfo\n#8162)
    getresults(getresults) ----> |gRPC method|zebra-grpc
    results ----> getresults(getresults\n#8163)
    registerkeys(registerkeys) ----> |gRPC method|zebra-grpc
    register ----> registerkeys(registerkeys\n#8176)
    deletekeys(deletekeys) ----> |gRPC method|zebra-grpc
    delete ----> deletekeys(deletekeys\n#8235)
    clear ----> clearresults(clearresults\n#8235)
    clearresults ----> |gRPC method|zebra-grpc
    register ----> scan
    results ----> scan
    subscribe ----> scan
    clear ----> |Not yet implemented|scan
    scan(scan\n#8256) ---> |gRPC push interface|zebra-grpc
    status ----> getstatus
    getstatus(getstatus\n#8258) ----> |gRPC method|zebra-grpc
    
    zebra-grpc([zebra-grpc]) ----> |username/password|client-auth(Client Auth\n#8164)
    zebra-grpc ----> |Address, port, etc|config(Configuration)
    zebra-grpc ----> |Encryption, TLS|server-auth(Server Auth)
    zebra-grpc ----> |All tests for the system|testing(Testing)
    
    zebrad([zebrad]) ----> |Zebrad starts the \nblockchain scanner task|zebra-scan
    zebrad ----> |Zebrad starts the grpc server\n#8241|zebra-grpc

    testing ---> |grpc responses|snapshots(gRPC Snapshots\n#8244)
    testing ---> |grpc requests & responses|grpc-unit(gRPC Unit tests\n#8244)
    testing ---> |service requests & responses|service-unit(Service Unit tests\nDone with each service impl)
    testing ---> |client|acceptance(Acceptance with state tests\n#8274 + #8259)
    testing ---> |grpcurl|manual(Manual testing\nDone with each grpc method impl)

    subgraph commands [Interaction between the services and the Scan Task]
        zebrad -..-> |Scan keys in the config|start-scan-task{{Start scan Task}}
        register -.-> start-scan-task
        delete -..-> stop-scan-task{{Stop scan task}}
        subscribe -..-> subscribe-scan-task{{Subscribe scan task}}
        zebra-scan --> scan-task{{Scan Task}}
        scan-task --> subscribe-scan-task
        scan-task --> start-scan-task
        scan-task --> stop-scan-task
        scan-task-refactor(Scan task refactor \n#8250) ----> scan-task
    end

    %% color of the nodes
    style zebra-scan fill:#8856eb
    style zebra-node-services fill:#8856eb
    style requests/responses fill:#8856eb
    style info fill:#8856eb
    style getinfo fill:#8856eb
    style results fill: #8856eb
    style getresults fill: #8856eb
    style register fill: #8856eb
    style registerkeys fill: #8856eb
    style zebra-grpc fill:#8856eb
    style delete fill:#8856eb
    style clear fill:#8856eb
    style deletekeys fill:#8856eb
    style clearresults fill:#8856eb
    style subscribe fill: #8856eb
    style zebrad fill: #8856eb
    style scan fill:#8856eb
    
    style config fill:#8856eb
    style testing fill:#8856eb

    style scan-task fill:#8856eb
    style start-scan-task fill:#8856eb
    style stop-scan-task fill:#8856eb
    style subscribe-scan-task fill:#8856eb

    style manual fill:#8856eb
    style acceptance fill:#238636
    style snapshots fill:#8856eb
    style grpc-unit fill:#8856eb
    style service-unit fill:#8856eb
```

## Formal specification

The formal specification of the system is defined using PlusCal, which is then translated into TLA+. The goal is to model check the system using TLC, ensuring correctness and reliability.

- [PlusCal script and TLA+ translation](grpc.tla)
- [Model Constants config file](grpc.cfg)
- [Generated specification PDF](grpc.pdf)

### Usage

To perform model checking, users can utilize tools such as the TLA+ toolbox or [VS Code extension](https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus). Follow these steps for VS Code extension:

1. Open the `grpc.cfg` file and specify the constants according to the desired configuration.
2. Open `grpc.tla` in the editor and execute the "TLA+: parse module" command.
3. Execute the "TLA+: Check model with TLC" command to initiate model checking. The output will be displayed in a new window.

An empty configuration will look as:

```
SPECIFICATION Spec
CONSTANT defaultInitValue = defaultInitValue
\* Add statements after this line.
CONSTANT ConfigViewingKeys = {}
CONSTANT GrpcViewingKeysBatch1 = {}
CONSTANT GrpcViewingKeysBatch2 = {}
CONSTANT GrpcViewingKeysBatch3 = {}

CONSTANT MaxScanTasks = 2
```

![image info](tla1.png)

A much more bigger instance of the spec can be model checked with for example, the following configuration:

```
SPECIFICATION Spec
CONSTANT defaultInitValue = defaultInitValue
\* Add statements after this line.
CONSTANT ConfigViewingKeys = {"vk1", "vk2"}
CONSTANT GrpcViewingKeysBatch1 = {"vk3", "vk4", "vk5"}
CONSTANT GrpcViewingKeysBatch2 = {"vk5", "vk6"}
CONSTANT GrpcViewingKeysBatch3 = {"vk5"}

CONSTANT MaxScanTasks = 10
```

![image info](tla2.png)

## Conclusion

The Zebra gRPC scanner specification provides a detailed overview of the system's design and functionality. While this document serves as an initial version, there are opportunities for improvement, such as adding invariants and exploring the full potential of TLA+ for verifying liveness and correctness. This project represents a step towards utilizing formal methods for ensuring the reliability of Zebra's core components.
