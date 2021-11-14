package GUI;

import javax.swing.JFrame; //imports JFrame library
import javax.swing.JButton; //imports JButton library
import java.awt.GridLayout; //imports GridLayout library
import javax.swing.*;
import java.awt.*;
import java.awt.event.*;
import java.io.*;


public class LOGExecutionMap {
	static int rows=10, cols=10;
	JFrame frame=new JFrame(); //creates frame
	JTextArea[][] grid; //names the grid of buttons
	static Cell [][] matrix;
	JPanel panGrid;
	JTextField currentAction;

	public LOGExecutionMap(){//constructor
		frame.setLayout(new BorderLayout());
		setupMatrix();
		Container c = frame.getContentPane();
		c.setLayout(new BorderLayout());

		JPanel newPan = new JPanel();
		currentAction = new JTextField ("Current Action");
		newPan.setLayout(new BorderLayout());
		newPan.add(currentAction);
		c.add(newPan);

		buttonMatrix(rows, cols);

		JPanel newPan2 = new JPanel();
		JButton nextAction = new JButton("Next Action");
		newPan2.setLayout(new BorderLayout());
		newPan2.add(nextAction);
		nextAction.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				System.out.println("A");
			}});
		c.add(newPan2);

		frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		frame.pack(); //sets appropriate size for frame
		frame.setVisible(true); //makes frame visible
	}

	public void buttonMatrix(int width, int length){
		panGrid = new JPanel();

		grid=new JTextArea[width][length]; //allocate the size of grid
		for(int x=0; x<width; x++){
			for(int y=0; y<length; y++){
				grid[x][y]=new JTextArea(
				"[x:"+x+"]"+"[y:"+y+"]"+ "\n" +
				"Content: " + matrix[x][y].getContent() + "\n" +
				"Deduced: " + matrix[x][y].getDeduction() + "\n" +
				"Probability: " + matrix[x][y].getProb());
				//grid[x][y].setFont(new Font("Arial", Font.PLAIN, 1));
				grid[x][y].setPreferredSize(new Dimension(100, 70));
				panGrid.add(grid[x][y]); //adds textArea to grid
			}
		}
	}

		private void setupMatrix (){
			matrix = new Cell[rows][cols];
			for (int i=0; i< rows; i++)
			for (int j=0; j<cols; j++)
			matrix[i][j]=new Cell();
		}

		/*
		private void saveMap(){
		File file = new File("mapEnvironment.clp");
		file.createNewFile();
		FileWriter writer = new FileWriter(file);
		writer.write("(deffacts battle-field\n");
		writer.write(")\n");
		writer.flush();
		writer.close();
	}*/

	public static void main(String[] args) {
		LOGExecutionMap window = new LOGExecutionMap();
	}
	public class Cell {
		String content;
		String deduction;
		double prob;
		boolean known;
		public Cell(){
			content = "none";
			known = true;
			deduction = "none";
			prob = 0;
		}
		public String getContent() {
			return content;
		}
		public void setContent(String cont) {
			content = cont;
		}
		public String getDeduction() {
			return deduction;
		}
		public void setDeduction(String deduct) {
			deduction = deduct;
		}
		public double getProb() {
			return prob;
		}
		public void setProb(double prob2) {
			prob = prob2;
		}
	}
}
