package fr.istic.cal.while1cons

import scala.util.Try

/**
 * définition d'une exception pour le cas des listes vides
 */
case object ExceptionListeVide extends Exception

/**
 * définition d'une exception pour le cas des listes de tailles différentes
 */
case object ExceptionListesDeLongueursDifferentes extends Exception

object While1cons {

 

  /**
   * UN ELIMINATEUR D'EXPRESSIONS COMPLEXES POUR LE LANGAGE WHILE
   *
   */

  /**
   *  TRAITEMENT DES EXPRESSIONS DU LANGAGE WHILE
   */

  /**
   * @param expression : un AST décrivant une expression du langage WHILE
   * @return une paire constituée d'une liste d'affectations ayant le même effet
   * que l'expression et de la variable qui contient le résultat
   */
  def while1ConsExprV(expression: Expression): (List[Command], Variable) = {
    
    expression match {
      case Nl => {
        val An : Variable = NewVar.make()
        (List(Set(An , Nl)), An)
      }
     
      case Cst(name) => {
        val An : Variable = NewVar.make()
        (List(Set(An , Cst(name))), An)
      }
     
      case VarExp(name) => (Nil, Var(name))
      case Cons(exp1, exp2) => {
        var resE1 = while1ConsExprV(exp1)
        var resE2 = while1ConsExprV(exp2)
        (resE1, resE2) match {
          case ((_,Var(name1)), (_,Var(name2))) => val An : Variable = NewVar.make();
                                                    ((resE1._1 ++ resE2._1 ++ List(Set(An, Cons(VarExp(name1), VarExp(name2))))), An)
        }
      }
      case Hd(exp) => {
        var res = while1ConsExprV(exp)
        res match {
          case (_,Var(name1)) => val An : Variable = NewVar.make();
                                 (res._1 ++ List(Set(An, Hd(VarExp(name1)))), An)
        }
      }
      case Tl(exp) => {
        var res = while1ConsExprV(exp)
        res match {
          case (_,Var(name1)) => val An : Variable = NewVar.make();
                                 (res._1 ++ List(Set(An, Tl(VarExp(name1)))), An)
        }
      }
      case Eq(exp1, exp2) => {
        var resE1 = while1ConsExprV(exp1)
        var resE2 = while1ConsExprV(exp2)
        (resE1, resE2) match {
          case ((_,Var(name1)), (_,Var(name2))) => val An : Variable = NewVar.make();
                                                    ((resE1._1 ++ resE2._1 ++ List(Set(An, Eq(VarExp(name1), VarExp(name2))))), An)
        }
      }
    }
  }

  /**
   * @param expression : un AST décrivant une expression du langage WHILE
   * @return une paire constituée d'une liste d'affectations et une expression simple
   * qui, combinées, ont le même effet que l'expression initiale
   */
  def while1ConsExprSE(expression: Expression): (List[Command], Expression) = {
    expression match {
      case Nl => (Nil , Nl)
      case Cst(name) => (Nil,Cst(name))
      case VarExp(name) => (Nil,VarExp(name))
      case Cons(exp1, exp2) => {
        val resE1 = while1ConsExprV(exp1)
        val resE2 = while1ConsExprV(exp2)
        (resE1, resE2) match {
          case ((_,Var(name1)), (_,Var(name2))) => ((resE1._1 ++ resE2._1 ), Cons(VarExp(name1), VarExp(name2)))
        }
      }
      case Hd(expr) => {
        var res = while1ConsExprV(expr)
        res match {
          case (_,Var(name1)) => (res._1 , Hd(VarExp(name1)))
        }
      }
      case Tl(expr) => {
        var res = while1ConsExprV(expr)
        res match {
          case (_,Var(name1)) => (res._1 , Tl(VarExp(name1)))
        }
      }
      case Eq(expr1, expr2) => {
        var resE1 = while1ConsExprV(expr1)
        var resE2 = while1ConsExprV(expr2)
        (resE1, resE2) match {
          case ((_,Var(name1)), (_,Var(name2))) =>  (resE1._1 ++ resE2._1, Eq(VarExp(name1) , VarExp(name2)))
        }
      }
    }
  }

  /**
   *
   *  TRAITEMENT DES COMMANDES DU LANGAGE WHILE
   */
  /**
   * @param command : un AST décrivant une commande du langage WHILE
   * @return une liste de commandes ayant un seul constructeur par expression
   * et ayant le même effet que la commande initiale
   */
  def while1ConsCommand(command: Command): List[Command] = {
    command match {
      case Nop => Nop :: Nil
      case Set(variable,expr) => {
        val paire = while1ConsExprSE(expr)
        paire._1 ++ List(Set(variable,paire._2))
      }
      case While(cond,body) => {
        val paire1 = while1ConsExprV(cond)
        val l_commands = while1ConsCommands(body)
        paire1._2 match { // variable qui contient le résultat paire1._1
          case Var(name) => paire1._1 ++ List(While(VarExp(name) , l_commands ++ paire1._1))
        }
      }
      case For(count,body) =>  {
        val paire1  = while1ConsExprV(count)
        val l_commands = while1ConsCommands(body)
        paire1._2 match { // variable qui contient le résultat paire1._1
          case Var(name) => paire1._1 ++ List(For(VarExp(name) , l_commands))
        }
      }
      case If(cond,then_commands,else_commands) => {
        val paire1 = while1ConsExprV(cond)
        val l_commands1 = while1ConsCommands(then_commands)
        val l_commands2 = while1ConsCommands(else_commands)
        paire1._2 match { // variable qui contient le résultat paire1._1
          case Var(name) => paire1._1 ++ List(If(VarExp(name),l_commands1,l_commands2))
        }
      }
    }
  }

  /**
   * @param commands : une liste non vide d'AST décrivant une liste non vide de commandes du langage WHILE
   * @return une liste de commandes ayant un seul constructeur par expression
   * et ayant le même effet que les commandes initiales
   */
  def while1ConsCommands(commands: List[Command]): List[Command] = {
    commands match {
      case Nil => throw ExceptionListeVide
      case commande :: Nil => while1ConsCommand(commande)
      case commande :: reste => while1ConsCommand(commande) ++ while1ConsCommands(reste)
      
    }
  }

  /**
   *
   *  TRAITEMENT DES PROGRAMMES DU LANGAGE WHILE
   */

  /**
   * @param program : un AST décrivant un programme du langage WHILE
   * @return un AST décrivant un programme du langage WHILE 
   * de même sémantique que le programme initial mais ne contenant que des expressions simples
   */
  def while1ConsProgr(program: Program): Program = {
    program match {
      case Progr(in,body,out) => Progr(in,while1ConsCommands(body),out)
    }
  }

  def main(args: Array[String]): Unit = {
    
    // vous pouvez ici tester manuellement vos fonctions par des print

  }
  
  
   /**
   * UTILISATION D'UN ANALYSEUR SYNTAXIQUE POUR LE LANGAGE WHILE
   *
   * les 3 fonctions suivantes permettent de construire un arbre de syntaxe abstraite
   * respectivement pour une expression, une commande, un programme
   */

  /**
   * @param s : une chaine de caractères représentant la syntaxe concrète d'une expression du langage WHILE
   * @return un arbre de syntaxe abstraite pour cette expression
   */
  def readWhileExpression(s: String): Expression = { WhileParser.analyserexpression(s) }

  /**
   * @param s : une chaine de caractères représentant la syntaxe concrète d'une commande du langage WHILE
   * @return un arbre de syntaxe abstraite pour cette commande
   */
  def readWhileCommand(s: String): Command = { WhileParser.analysercommand(s) }

  /**
   * @param s : une chaine de caractères représentant la syntaxe concrète d'un programme du langage WHILE
   * @return un arbre de syntaxe abstraite pour ce programme
   */
  def readWhileProgram(s: String): Program = { WhileParser.analyserprogram(s) }
  
}