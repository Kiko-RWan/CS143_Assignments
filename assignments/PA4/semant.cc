

#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"
#include <vector>

extern int semant_debug;
extern char *curr_filename;


static int semant_errors = 0;
static ostream& error_stream = cerr;

typedef std::map<Symbol, Class_> NameClassMap;
NameClassMap name_class_map;
std::map<Symbol, Symbol> parent_map;


typedef SymbolTable<Symbol, Symbol> ObjectEnvironment; // name to type
ObjectEnvironment objectEnv;

typedef std::vector<method_class*> Methods;
typedef std::map<Class_, Methods> MethodTable;
MethodTable methodTable;

typedef std::map<Symbol, Class_> NameClassMap;

static ostream& semant_error()                  
{                                                 
    semant_errors++;                            
    return error_stream;
} 

static ostream& semant_error(Symbol filename, tree_node *t)
{
    error_stream << filename << ":" << t->get_line_number() << ": ";
    return semant_error();
}

static ostream& semant_error(Class_ c)
{                                                             
    return semant_error(c->get_filename(),c);
}    

//////////////////////////////////////////////////////////////////////
//
// Symbols
//
// For convenience, a large number of symbols are predefined here.
// These symbols include the primitive type and method names, as well
// as fixed names used by the runtime system.
//
//////////////////////////////////////////////////////////////////////
static Symbol 
    arg,
    arg2,
    Bool,
    concat,
    cool_abort,
    copy,
    Int,
    in_int,
    in_string,
    IO,
    length,
    Main,
    main_meth,
    No_class,
    No_type,
    Object,
    out_int,
    out_string,
    prim_slot,
    self,
    SELF_TYPE,
    Str,
    str_field,
    substr,
    type_name,
    val;
//
// Initializing the predefined symbols.
//
static void initialize_constants(void)
{
    arg         = idtable.add_string("arg");
    arg2        = idtable.add_string("arg2");
    Bool        = idtable.add_string("Bool");
    concat      = idtable.add_string("concat");
    cool_abort  = idtable.add_string("abort");
    copy        = idtable.add_string("copy");
    Int         = idtable.add_string("Int");
    in_int      = idtable.add_string("in_int");
    in_string   = idtable.add_string("in_string");
    IO          = idtable.add_string("IO");
    length      = idtable.add_string("length");
    Main        = idtable.add_string("Main");
    main_meth   = idtable.add_string("main");
    //   _no_class is a symbol that can't be the name of any 
    //   user-defined class.
    No_class    = idtable.add_string("_no_class");
    No_type     = idtable.add_string("_no_type");
    Object      = idtable.add_string("Object");
    out_int     = idtable.add_string("out_int");
    out_string  = idtable.add_string("out_string");
    prim_slot   = idtable.add_string("_prim_slot");
    self        = idtable.add_string("self");
    SELF_TYPE   = idtable.add_string("SELF_TYPE");
    Str         = idtable.add_string("String");
    str_field   = idtable.add_string("_str_field");
    substr      = idtable.add_string("substr");
    type_name   = idtable.add_string("type_name");
    val         = idtable.add_string("_val");
}

static void add_class(Class_ c) {
    Symbol name = c->get_name();
    Symbol parent = c->get_parent();

    if(name == SELF_TYPE) {
        semant_error(c) << "Redefinition of basic class SELF_TYPE." << endl;
    }
    else if(name_class_map.count(name)) {
        semant_error(c) << "Class " << name << " was previously defined." << endl;
    }
    else if (parent == Int || parent == Str || parent == Bool || parent == SELF_TYPE) {
        semant_error(c) << "Class " << name << " cannot inherit class " << parent << "." << endl;
    }
    else {
        name_class_map[name] = c;
        parent_map[name] = parent;         
    }
}

static void install_basic_classes() {

    // The tree package uses these globals to annotate the classes built below.
   // curr_lineno  = 0;
    Symbol filename = stringtable.add_string("<basic class>");
    
    // The following demonstrates how to create dummy parse trees to
    // refer to basic Cool classes.  There's no need for method
    // bodies -- these are already built into the runtime system.
    
    // IMPORTANT: The results of the following expressions are
    // stored in local variables.  You will want to do something
    // with those variables at the end of this method to make this
    // code meaningful.

    // 
    // The Object class has no parent class. Its methods are
    //        abort() : Object    aborts the program
    //        type_name() : Str   returns a string representation of class name
    //        copy() : SELF_TYPE  returns a copy of the object
    //
    // There is no need for method bodies in the basic classes---these
    // are already built in to the runtime system.

    Class_ Object_class =
	class_(Object, 
	       No_class,
	       append_Features(
			       append_Features(
					       single_Features(method(cool_abort, nil_Formals(), Object, no_expr())),
					       single_Features(method(type_name, nil_Formals(), Str, no_expr()))),
			       single_Features(method(copy, nil_Formals(), SELF_TYPE, no_expr()))),
	       filename);

    // 
    // The IO class inherits from Object. Its methods are
    //        out_string(Str) : SELF_TYPE       writes a string to the output
    //        out_int(Int) : SELF_TYPE            "    an int    "  "     "
    //        in_string() : Str                 reads a string from the input
    //        in_int() : Int                      "   an int     "  "     "
    //
    Class_ IO_class = 
	class_(IO, 
	       Object,
	       append_Features(
			       append_Features(
					       append_Features(
							       single_Features(method(out_string, single_Formals(formal(arg, Str)),
										      SELF_TYPE, no_expr())),
							       single_Features(method(out_int, single_Formals(formal(arg, Int)),
										      SELF_TYPE, no_expr()))),
					       single_Features(method(in_string, nil_Formals(), Str, no_expr()))),
			       single_Features(method(in_int, nil_Formals(), Int, no_expr()))),
	       filename);  

    //
    // The Int class has no methods and only a single attribute, the
    // "val" for the integer. 
    //
    Class_ Int_class =
	class_(Int, 
	       Object,
	       single_Features(attr(val, prim_slot, no_expr())),
	       filename);

    //
    // Bool also has only the "val" slot.
    //
    Class_ Bool_class =
	class_(Bool, Object, single_Features(attr(val, prim_slot, no_expr())),filename);

    //
    // The class Str has a number of slots and operations:
    //       val                                  the length of the string
    //       str_field                            the string itself
    //       length() : Int                       returns length of the string
    //       concat(arg: Str) : Str               performs string concatenation
    //       substr(arg: Int, arg2: Int): Str     substring selection
    //       
    Class_ Str_class =
	class_(Str, 
	       Object,
	       append_Features(
			       append_Features(
					       append_Features(
							       append_Features(
									       single_Features(attr(val, Int, no_expr())),
									       single_Features(attr(str_field, prim_slot, no_expr()))),
							       single_Features(method(length, nil_Formals(), Int, no_expr()))),
					       single_Features(method(concat, 
								      single_Formals(formal(arg, Str)),
								      Str, 
								      no_expr()))),
			       single_Features(method(substr, 
						      append_Formals(single_Formals(formal(arg, Int)), 
								     single_Formals(formal(arg2, Int))),
						      Str, 
						      no_expr()))),
	       filename);

    add_class(Object_class);
    add_class(IO_class);
    add_class(Int_class);
    add_class(Bool_class);
    add_class(Str_class);
}

////////////////////////////////////////////////////////////////////
//
// semant_error is an overloaded function for reporting errors
// during semantic analysis.  There are three versions:
//
//    ostream& ClassTable::semant_error()                
//
//    ostream& ClassTable::semant_error(Class_ c)
//       print line number and filename for `c'
//
//    ostream& ClassTable::semant_error(Symbol filename, tree_node *t)  
//       print a line number and filename
//
///////////////////////////////////////////////////////////////////

// 检查环和父类存在
static void check_inheritance() {
    for (auto it = parent_map.begin(); it != parent_map.end(); it++){
        Symbol child = it->first;
        Symbol parent = it->second;

        // 根为No_class
        while (parent != No_class){
            // 存在环
            if (parent == child){
                semant_error(name_class_map[child]) << "Has cycle!" << endl;
                return;
            }
            // 不存在父节点
            if (!parent_map.count(parent)){
                semant_error(name_class_map[child]) << "Doesn't contain parent!" << endl;
                return;
            }
            parent = parent_map[parent];
        }
    }
}

static void check_main() {
    bool main_class_flag = false;
    bool main_method_flag = false;

    for (auto it = name_class_map.begin(); it != name_class_map.end(); it++){
        Symbol name = it->first;
        Class_ c = it->second;
        if (name == Main){
            main_class_flag = true;
            Features features = c->get_features();
            for (auto i = features->first(); features->more(i); i = features->next(i)){
                Feature feature = features->nth(i);
                if (feature->is_method() && feature->get_name() == main_meth){
                    main_method_flag = true;
                    break;
                }
            }
            break;
        }
    }

    if (!main_class_flag){
        semant_error() << "No main class!" << endl;
    }
    else if(!main_method_flag){
        semant_error() << "No 'main' method in class Main." << endl;
    }
}

static void install_methods() {
    for(auto it : name_class_map) {
        Features features = it.second->get_features();
        Methods methods;
        for (auto i = features->first(); features->more(i); i = features->next(i)){
            Feature feature = features->nth(i);
            if (feature->is_method()){
                method_class* method = static_cast<method_class*>(feature);

                bool existed = false;
                for (auto j = methods.begin(); j != methods.end(); j++){
                    if (method->get_name() == (*j)->get_name()){
                        existed = true;
                        break;
                    }
                }
                if (!existed){
                    methods.push_back(method);
                }
                else {
                    semant_error((Class_)method) << "Method " << method->get_name() << " is multiply defined." << endl;
                }
            }
        }
        methodTable[it.second] = methods;
    }
}

/*   This is the entry point to the semantic checker.

     Your checker should do the following two things:

     1) Check that the program is semantically correct
     2) Decorate the abstract syntax tree with type information
        by setting the `type' field in each Expression node.
        (see `tree.h')

     You are free to first do 1), make sure you catch all semantic
     errors. Part 2) can be done in a second stage, when you want
     to build mycoolc.
 */
void program_class::semant()
{
    initialize_constants();

    install_basic_classes();
    for (int i = classes->first(); classes->more(i); i = classes->next(i)) {
        add_class(classes->nth(i));
    }

    /* some semantic analysis code may go here */
    check_inheritance();
    if (semant_errors > 0) {
        cerr << "Compilation halted due to static semantic errors." << endl;
        exit(1);
    }

    check_main();
    if (semant_errors > 0) {
        cerr << "Compilation halted due to static semantic errors." << endl;
        exit(1);
    }

    install_methods();

    if (semant_errors) {
        cerr << "Compilation halted due to static semantic errors." << endl;
        exit(1);
    }
}
