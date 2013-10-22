package de.agra.sat.koselleck.utils;

/** imports */
import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.PrintWriter;

/**
 * 
 * @author Max Nitze
 */
public abstract class IOUtils {
	/**
	 * 
	 * @param uri
	 * 
	 * @return
	 */
	public static String readFromFile(String uri) {
		InputStream resourceStream = IOUtils.class.getResourceAsStream(uri);
		return readFromStream(resourceStream);
	}
	
	/**
	 * 
	 * @param inputStream
	 * 
	 * @return
	 */
	public static String readFromStream(InputStream inputStream) {
		BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(inputStream));
		StringBuilder stringBuilder = new StringBuilder();
		String line = null;
		try {
			while((line = bufferedReader.readLine()) != null) {
				stringBuilder.append(line);
				stringBuilder.append("\n");
			}
		} catch (IOException e1) {
			e1.printStackTrace();
		} finally {
			try {
				bufferedReader.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
		
		return stringBuilder.toString();
	}
	
	/**
	 * 
	 * @param uri
	 * @param text
	 */
	public static void writeToFile(String uri, String text) {
		PrintWriter out = null;
		try {
			out = new PrintWriter(uri);
			out.println(text);
			out.flush();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} finally {
			out.close();
		}
	}
	
	/**
	 * 
	 * @param outputStream
	 * @param text
	 */
	public static void writeToOutputStream(OutputStream outputStream, String text) {
		PrintWriter out = null;
		try {
			out = new PrintWriter(outputStream);
			out.println(text);
			out.flush();
		} finally {
			out.close();
		}
	}
}
