# Use an official Python runtime as a parent image
FROM python:3.9-slim

# Set the working directory in the container
WORKDIR /app

# Copy requirements.txt first to leverage Docker cache
COPY requirements.txt .

# Install dependencies
RUN pip install --no-cache-dir -r requirements.txt

# Copy the rest of the application code
COPY . .

# Expose port 8080 for the Flask app (as expected by fly.toml)
EXPOSE 8080

# Use Gunicorn to serve the Flask app, binding to port 8080
CMD ["gunicorn", "--bind", "0.0.0.0:8080", "app:app"]
