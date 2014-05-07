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
 * IOUtils provides functions to read and write from any kind of files.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public final class IOUtils {
	/**
	 * Private Constructor to prevent this class from being instantiated.
	 */
	private IOUtils() {}

	/**
	 * readFromFile reads the file at the given {@code URI} and returns its
	 *  content.
	 * 
	 * @param uri the {@code URI} to the file to read from
	 * 
	 * @return the content of the file at the given {@code URI}
	 * 
	 * @throws IOException if the file is not readable
	 */
	public static String readFromFile(String uri) throws IOException {
		InputStream resourceStream = IOUtils.class.getResourceAsStream(uri);
		return readFromStream(resourceStream);
	}

	/**
	 * readFromStream reads from the given stream and returns its content.
	 * 
	 * @param inputStream the input stream to read from
	 * 
	 * @return the content of the given input stream
	 * 
	 * @throws IOException if the stream is not readable
	 */
	public static String readFromStream(InputStream inputStream) throws IOException {
		BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(inputStream));
		StringBuilder stringBuilder = new StringBuilder();
		String line = null;
		while((line = bufferedReader.readLine()) != null) {
			stringBuilder.append(line);
			stringBuilder.append("\n");
		}
		bufferedReader.close();

		return stringBuilder.toString();
	}

	/**
	 * writeToFile writes the given text to the file at the given {@code URI}.
	 * 
	 * @param uri the {@code URI} to the file to write to
	 * @param text the text to write to the file at the given {@code URI}
	 * 
	 * @throws IOException if the file at the given {@code URI} does not exist
	 *  (and can not be created)
	 */
	public static void writeToFile(String uri, String text) throws FileNotFoundException {
		PrintWriter printWriter = new PrintWriter(uri);
		printWriter.println(text);
		printWriter.flush();
		printWriter.close();
	}

	/**
	 * writeToStream writes the given text to the given output stream.
	 * 
	 * @param outputStream the output stream to write to
	 * @param text the text to write to the output stream
	 */
	public static void writeToStream(OutputStream outputStream, String text) {
		PrintWriter printWriter = new PrintWriter(outputStream);
		printWriter.println(text);
		printWriter.flush();
		printWriter.close();
	}
}
