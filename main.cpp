#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <sstream>
#include <unordered_map>
#include <algorithm>
#include <cstdlib>
#include <cstdint>
#include "cadical.hpp"
//#include <assert.h> //debug

// Var set is a bit set used to save variable occurances within a subtree
// ONLY decision variables!
using VarSet = std::vector<uint64_t>;
int MAX_VAR = 0;
int MAX_ID = 0;
typedef std::vector<std::vector<int>> cnf;

void error( std::string line ) {
    std::cerr << line << std::endl;
    exit( EXIT_FAILURE );
}

VarSet empty_varset() {
    return VarSet( ( MAX_VAR + 63 ) / 64, 0 );
}

void add_var( VarSet& vars, int v ) {
    if( v <= 0 || v > MAX_VAR )
        error( "Invalid var for bitset: " + std::to_string( v ) );
    int bit = v - 1;
    int word = bit / 64;
    int offset = bit % 64;
    vars[word] |= ( 1ULL << offset );
}

void union_vars( VarSet& dst, const VarSet& src ) {
    for( size_t i = 0; i < dst.size(); ++i )
        dst[i] |= src[i];
}

// Representation of nodes of the d-DNNF
struct Node {
    enum Type : unsigned short { DEC, AND, ONE, ZERO } type;
    // Children for AND-gates
    std::vector<int> children;
    // Deciding variable for DECISION-gates
    int var = 0;
    // Children if var is true or false
    int high, low = 0;
    
    // CORE OF THE PROOF SYSTEM: Labelling each node with
    // a CNF which meets the requirements (i)-(vi)
    cnf label;

    // Varset to compute vars of the subformula + flag if Varset has been setup
    VarSet vars;
    bool vars_are_set = false;
};

// Representation of the D4 specific arcs
// Auxiliary for the parse_nodes function
struct Arc {
    int dst;
    std::vector<int> lits;
};

std::string to_string( cnf form ) {
    std::stringstream stream;
    for( auto& clause : form ) {
        for( auto& lit : clause ) {
            stream << lit << " ";
        }
        stream << std::endl;
    }
    return stream.str();
}

/**
     Parse a line of a cnf-File into a vector of literals.
     @param line, a string that represents a cnf clause.
     \return a vector of integers that is sorted and does not contain dublicates.
  */
std::vector<int> parse_clause( std::string& line ) {
    std::vector<int> clause;
    std::istringstream stream( line );
    int lit;
    while( stream >> lit ) {
        if( lit == 0 ) break;
        clause.push_back( lit );
        MAX_VAR = std::max( MAX_VAR, std::abs( lit ) );
    }
    std::sort( clause.begin(), clause.end() );
    clause.erase( std::unique( clause.begin(), clause.end() ), clause.end() );
    return clause;
}


/**
     Checker wether a cnf-formula is unsatisfiable using Cadical.
     @param cnf, a cnf.
     \return true if unsatisfiable, false if satisfiable.
  */
bool unsat( const cnf& form ) {
    CaDiCaL::Solver solver;
    solver.set("factor", 0);
    solver.set("factorcheck", 0);

    for( auto& clause : form ) {
        for( int lit : clause ) {
            solver.add( lit );
        }
        solver.add(0);
    }

    int res = solver.solve();
    return res == 20;
}


/**
     Checker wether a cnf-formula is a tautology using Cadical.
     @param cnf, a cnf.
     \return true if tautology, false if not.
  */
bool taut( const cnf& form ) {
    CaDiCaL::Solver solver;
    solver.set( "factor", 0 );
    solver.set( "factorcheck", 0 );

    for( auto& clause : form ) {
        for( auto& lit : clause ) {
            solver.add( -lit );
            solver.add( 0 );
        }
    }

    int res = solver.solve();
    return res == 20;
}


// Help function for the help function build_subtree
std::vector<Arc> filter_arcs(   std::vector<Arc>    i_arcs,
                                int                 var )
{
    std::vector<Arc> o_arcs;

    for( auto& arc : i_arcs ) {
        bool drop = false;
        Arc tmp = arc;

        tmp.lits.erase(
            std::remove_if( tmp.lits.begin(), tmp.lits.end(),
                [&](int lit)
                {
                    // Case 1: Literal in arch -> erase
                    if( lit ==  var )
                        return true;

                    // Case 2: Negation in arch -> erase whole arch
                    if( lit == -var ) {
                        drop = true;
                        return true;
                    }
                    // Case 3: Different variable -> Keep
                    return false;

                }), tmp.lits.end() );

        if( !drop )
            o_arcs.push_back( std::move( tmp ) );
    }

    return o_arcs;
}

/** Help function for parse_nodes
    -)Pops a variable from vars, two recursions for vars=true and vars=false
    -)Creates new decisions nodes for further literals that require satisfaction
    -)Uses another help function (filter_arcs) to either remove satisfied literals, or
        leave out archs that contain the negation
    -)If all literals of an arch are satisfied -> Connect node to arch.dst
*/
void build_subtree( int                             root,
                    std::unordered_map<int, Node>&  nodes,
                    std::vector<Arc>&               arcs,
                    int                             false_node )
{
    Node& node = nodes[root];

    if( arcs.size() == 1 && arcs[0].lits.empty() ) {
        node.high = node.low = arcs[0].dst;
        return;
    }
    
    int var = abs(arcs[0].lits[0]);

    node.var = var;
    node.type = Node::DEC;
    
    // Case 1 var=true
    std::vector<Arc> arcs_high = filter_arcs( arcs, var );

    if( arcs_high.empty() ) {
        node.high = false_node;
    } else if( arcs_high.size() == 1 && arcs_high[0].lits.empty() ) {
        node.high = arcs_high[0].dst;
    } else {
        Node new_high;
        nodes[++MAX_ID] = std::move( new_high );
        node.high = MAX_ID;

        build_subtree( MAX_ID, nodes, arcs_high, false_node );
    }


    // Case 2 var=false
    std::vector<Arc> arcs_low = filter_arcs( arcs, -var );

    if( arcs_low.empty() ) {
        node.low = false_node;
    } else if ( arcs_low.size() == 1 && arcs_low[0].lits.empty() ) {
        node.low = arcs_low[0].dst;
    } else {
        Node new_low;
        nodes[++MAX_ID] = std::move( new_low );
        node.low = MAX_ID;

        build_subtree( MAX_ID, nodes, arcs_low, false_node );
    }
}

/** Help function 2 for parse_nodes:
    Computes the set of DECISION vars in the subtree of a node.
*/
VarSet derive_vars( int root, std::unordered_map<int, Node>& nodes ) {
    
    auto it = nodes.find( root );
    if( it == nodes.end() )
        error( "Node has an undefined child: " + std::to_string( root ) );
    Node& node = it->second;

    if( node.vars_are_set ) return node.vars;
    node.vars = empty_varset();

    if( node.type == Node::DEC ) {
        union_vars( node.vars, derive_vars( node.low, nodes ) );
        union_vars( node.vars, derive_vars( node.high, nodes ) );
        if( node.var != 0 )
            add_var( node.vars, std::abs( node.var ) );
    }

    if( node.type == Node::AND ) {
        for( int child : node.children ) {
            VarSet child_vars = derive_vars( child, nodes );
            union_vars( node.vars, child_vars );
        }
    }
    
    node.vars_are_set = true;
    return node.vars;
}


/**
     Parse a d-DNNF in String representation into a vector of nodes.
     @param lines, a vector of strings that represents a d-DNNF.
     @param nodes, an unordered map matching of IDs to their nodes.
     \return the root node.
  */
int parse_nodes(    std::vector<std::string>&       lines,
                    std::unordered_map<int, Node>&  nodes ) {
    

    // Keeping track of the node ID in the last line -> root!
    int last_id = -1;
    int false_node = 0;
    int true_node = 0;
    
    // Arcs ordered by their source node
    std::unordered_map<int, std::vector<Arc>> arcs;

    // Phase 1: Create nodes and parse archs
    for( auto& line : lines ) {
        if( line.empty()    || 
            line[0] == 'c'  ||
            line[0] == 'p' ) continue;
        std::istringstream stream( line );
        std::string prefix;
        stream >> prefix;

        // Case 1: Node definition
        if( std::isalpha( prefix[0] ) ) {
            stream >> last_id;
            Node node;

            switch( prefix[0] ) {
                case 'o': node.type = Node::DEC; break;
                case 'a': node.type = Node::AND; break;
                case 't': node.type = Node::ONE; true_node = last_id; break;
                case 'f': node.type = Node::ZERO; false_node = last_id; break;
            }
            nodes[last_id] = std::move( node );
            MAX_ID = std::max( MAX_ID, last_id );

        // Case 2: Arch definition
        } else if( std::isdigit( prefix[0] ) ) {
            if( prefix[0] == '0' ) error( "Malformed line in nnf-file: " + line );
            Arc arc;
            int src = std::stoi( prefix );
            if( src < 1 ) error( "Malformed line in nnf-file: " + line );
            int dst;
            stream >> dst;
            if( dst < 1 ) error( "Malformed line in nnf-file: " + line );
            arc.dst = dst;
            int lit;
            while( stream >> lit && lit != 0 ) {
                arc.lits.push_back( lit );
                MAX_VAR = std::max( MAX_VAR, std::abs( lit ) );
            }
            arcs[src].push_back( std::move( arc ) );
            // D4 does not explicitly guarantee that arcs connect already definied nodes!
            MAX_ID = std::max( MAX_ID, std::max( src, dst ) );
            last_id = src;
        }
        else error( "Malformed line in nnf-file: " + line );

    }

    if( false_node == 0 ) {
        Node node;
        node.type = Node::ZERO;
        node.label = {{}};
        nodes[++MAX_ID] = std::move( node );
        false_node = MAX_ID;
    }

    if( true_node == 0 ) {
        Node node;
        node.type = Node::ONE;
        nodes[++MAX_ID] = std::move( node );
        true_node = MAX_ID;
    }

    // Phase 2: Decompose arcs for standard Darwiche-Style representation
    for( auto& [srcID, arcList] : arcs ) {
        if( nodes.find( srcID ) == nodes.end() )
            error( "Arc refers to undefined node " + std::to_string( srcID ) );
        Node& src = nodes.at( srcID );

        if( src.type == Node::AND ) {
            for( auto& arc: arcList )
                src.children.push_back( arc.dst );
            continue;
        }
        
        build_subtree(  srcID,
                        nodes,
                        arcList,
                        false_node );
    
    }

    derive_vars( last_id, nodes );

    return last_id;
}


// Help function I for proof_system
/**
     Check whether a node is already labeled, if yes, check equivalence to input label.
     For false-nodes: Check that input label is unsatisfiable -> nothing to set.
     @param node, a node to be checked.
     @param i_label, the label to be set.
     @param nodes, unordered map of nodes.
     \return boolean value: true: No caching; false: caching succesful (-> no need to recurse)
  */
bool apply_caching( int                             node,
                    const cnf&                      i_label,
                    std::unordered_map<int, Node>&  nodes ) {

    auto& l_node = nodes[node];
    auto& l_label = l_node.label;

    if( !l_label.empty() ) {
        if( l_node.type == Node::ZERO ) {
            if( l_label.size() == 1 && l_label[0].empty() ) return false;
            if( !unsat( i_label ) ) {
                error( "Label satisfiable at false node: " + std::to_string( node ) + 
                        "\nWith clauses: " + to_string( i_label ) );
            }
            return false;
        }
        if( l_label != i_label ) {
            std::cout << "expected: " + to_string( i_label )  << std::endl;
            std::cout << "found: " + to_string( l_label ) << std::endl;
            error( "Cached label mismatch at node " + std::to_string( node ) );
        }
        return false;
    }

    l_label = i_label;
    return true;
}


// Help function II for proof_system
cnf unit_propagation(   cnf form,
                        int lit ) {
    
    for( size_t i = 0; i < form.size(); i++ ) {
        auto& clause = form[i];

        // Case 1: literal in clause
        if( std::find( clause.begin(), clause.end(), lit ) != clause.end() ) {
            form.erase( form.begin() + i );
            i--;
            continue;
        }

        // Case 2: negation in clause
        clause.erase( std::remove( clause.begin(), clause.end(), -lit ),
                clause.end()
        );

        // If Case 2, Contradiction created?
        if( clause.empty() ) {
            return cnf{ {} };
        }

    }
    std::sort( form.begin(), form.end() );
    form.erase( std::unique( form.begin(), form.end() ), form.end() );
    return form;
}


// Help function III for proof_system
// Check wether a varset contains var
inline bool has_var( const VarSet& vars, int v ) {
    int bit = v - 1;
    int word = bit / 64;
    int offset = bit % 64;
    return( vars[word] & ( 1ULL << offset ) ) != 0;
}

// Help function IV for proof_system (also uses III)
// Check wether a clause shares a variable with a varset
bool clause_intersects_vars(    const std::vector<int>& clause,
                                const VarSet& vars ) {
    for( auto& lit : clause )
        if( has_var( vars, std::abs( lit ) ) )
            return true;
    return false;
}

void extract_component( const cnf& i_label,
                        VarSet& vars,
                        cnf& o_label,
                        std::vector<bool>& used )
{
    bool changed = true;

    while( changed ) {
        changed = false;

        for( size_t i = 0; i < i_label.size(); i++ ) {
            if( used[i] ) continue;

            auto& clause = i_label[i];

            if( !clause_intersects_vars( clause, vars ) )
                continue;

            used[i] = true;
            o_label.push_back( clause );

            for( const auto& lit : clause ) {
                int var = std::abs( lit );
                if( !has_var( vars, var ) ) {
                    add_var( vars, var );
                    changed = true;
                }
            }
        }
    }
}

/**
     Label nodes recursively according to the proof system.
     @param root, root of the subtree (already labled).
     @param nodes, unordered_map of ids to their nodes.
  */
bool proof_system(  int                             i_root,
                    std::unordered_map<int, Node>&  nodes )
{
    Node& l_root = nodes[i_root];
    cnf& l_label = l_root.label;
    
    // Sort cnf topologically and erase dublicate clauses
    std::sort( l_label.begin(), l_label.end() );
    l_label.erase( std::unique( l_label.begin(), l_label.end() ), l_label.end() );
    
    if( l_root.type == Node::DEC ) {        
        int high = l_root.high;
        int low = l_root.low;

        if( l_root.var == 0 ) {
            if( high == low ) { // D4 algorithm sets root as a decision note with no literals
                nodes[high].label = l_label;
                return proof_system( high, nodes );
            } else error( "Decision node with no variable, but children " + 
                            std::to_string( low ) + " and " + std::to_string( high ) );
        }

        // Condition v
        bool high_recurse = apply_caching(  high,
                                            unit_propagation( l_label,  l_root.var ),
                                            nodes );
        bool low_recurse = apply_caching(   low,
                                            unit_propagation( l_label,  -l_root.var ),
                                            nodes );
        
        // Condition ii
        bool high_result = high_recurse ? proof_system( high, nodes ) : true;
        bool low_result = low_recurse ? proof_system( low,  nodes ) : true;

        if( !( high_result || low_result ) )
            error( "Decision node not connected to a true node: " + std::to_string( i_root ) );

        return true;
    }

    else if( l_root.type == Node::AND ) {
        const auto& parent_label = l_label;
        std::vector<bool> used( l_label.size(), false );

        for( int child : l_root.children ) {
            extract_component(  l_label,
                                nodes[child].vars,
                                nodes[child].label, 
                                used );
        }

        // Check that all clauses of the parent label have been assigned
        for( int i = 0; i < used.size(); i++ ) {
            if( !used[i] ) {
                std::cerr << "Clause at and-node not assigned at: " << i_root << std::endl;
                std::cerr << "Clause: ";
                for( auto& lit: l_label[i]) {
                    std::cerr << lit << " ";
                }
                std::cerr << std::endl << "With mother label: " << to_string( l_root.label ) << std::endl;
                std::cerr << "Unsatisfied: " << (l_root.label.size() == 1 && l_root.label[0].size() == 0) << std::endl;
                std::cerr << std::endl << "With children labels: " << std::endl;
                for( int i=0; i < l_root.children.size(); i++ ) {
                    std::cerr << "child " << i+1 << " :" << std::endl;
                    std::cerr << to_string( nodes[l_root.children[i]].label );
                }
                error( "Terminating" );
            }
        }

        // Check that childrens' labels are in pairs disjunctive
        for( size_t i = 0; i < l_root.children.size(); i++ ) {
            int child1 = l_root.children[i];

            for( size_t j = i + 1; j < l_root.children.size(); j++ ) {
                int child2 = l_root.children[j];

                const VarSet& v1 = nodes[child1].vars;
                const VarSet& v2 = nodes[child2].vars;

                for( size_t w = 0; w < v1.size(); w++ ) {
                    if( v1[w] & v2[w] ) {
                        error( "AND-node: variable overlap between children" + std::to_string( child1 )
                                + " and " + std::to_string( child2 ) );
                    }
                }
            }
        }

        // condition ii
        bool connected_to_true;
        for( auto& child: l_root.children ) {
            bool res = proof_system( child, nodes );
            connected_to_true = connected_to_true | res;
        }
        if( !connected_to_true )
            error( "And node not connected to a true node: " + std::to_string( i_root ) );
        return true;
    }

    else if( l_root.type == Node::ONE ) {
        if( !l_label.empty() ) {
            if( !taut( l_label ) )
                error( "True node not satisfied: ID: " + std::to_string( i_root ) + 
                        ", clauses: \n" + to_string( l_root.label ) );
        }
        return true;
    }

    else if( l_root.type == Node::ZERO ) {
        if( l_label.size() == 1 && l_label[0].empty() ) return false;
        if( !unsat( l_label ) ) {
                error( "Label satisfiable at false node: " + std::to_string( i_root ) + 
                        "\nWith clauses: " + to_string( l_label ) );
        }
    }
    return false;
}

int main( int argc,  char **argv )
{
    std::ifstream nnf_file( argv[1] );
    if ( !nnf_file ) {
        std::cerr << "Fehler: nnf Datei nicht gefunden" << std::endl;
        return 1;
    }

    std::ifstream cnf_file( argv[2] );
    if ( !cnf_file ) {
        std::cerr << "Fehler: cnf Datei nicht gefunden" << std::endl;
        return 1;
    }

    clock_t start = clock();

    std::vector<std::string> lines;
    cnf cnf;
    std::unordered_map<int, Node> nodes;
    int root;
    std::string line;

    std::cout << "Processing d-DNNF" << std::endl;

    while( std::getline( nnf_file, line ) ) {
        lines.push_back( line );
    }
    root = parse_nodes( lines, nodes );

    while( std::getline( cnf_file, line ) ) {
        // Skipping empty, header and commentary lines
        if( line.empty()   ||
            line[0] == 'c' ||
            line[0] == 'p' ) continue;
        cnf.push_back( parse_clause( line ) );
    }

    clock_t mid = clock();
    std::cout << "Preprocessing time: " << (float) ( mid - start ) / CLOCKS_PER_SEC << " seconds" << std::endl;


    // Actual application of the proof system
    nodes[root].label = cnf;
    std::cout << "Starting proof system" << std::endl;
    proof_system( root, nodes );
    std::cout << "Success!" << std::endl;

    clock_t end = clock();
    std::cout << "Proof time: " << (float)( end - mid ) / CLOCKS_PER_SEC << " seconds"  << std::endl;
    std::cout << "Total time: " << (float)( end - start ) / CLOCKS_PER_SEC << " seconds" << std::endl;

    return 0;
}

